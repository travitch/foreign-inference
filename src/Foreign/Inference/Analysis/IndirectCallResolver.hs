{-# LANGUAGE ViewPatterns, OverloadedStrings, FlexibleContexts #-}
-- | FIXME: Currently there is an exception allowing us to identify
-- finalizers that are called through function pointers if the
-- function pointer is global and has an initializer.
--
-- This needs to be generalized to cover things that are initialized
-- once in the library code with a finalizer.  This will be a lower-level
-- analysis that answers the query:
--
-- > initializedOnce :: Value -> Maybe Value
--
-- where the returned value is the single initializer that was sourced
-- within the library.  This can be the current simple analysis for
-- globals with initializers.  Others will be analyzed in terms of
-- access paths (e.g., Field X of Type Y is initialized once with
-- value Z).
--
-- Linear scan for all stores, recording their access path.  Also look
-- at all globals (globals can be treated separately).  If an access
-- path gets more than one entry, stop tracking it.  Only record
-- stores where the value is some global entity.
--
-- Run this analysis after or before constructing the call graph and
-- initialize the whole-program summary with it.  It doesn't need to
-- be computed bottom up as part of the call graph traversal.
module Foreign.Inference.Analysis.IndirectCallResolver (
  IndirectCallSummary,
  identifyIndirectCallTargets,
  indirectCallInitializers,
  indirectCallTargets
  ) where

import Control.Exception ( throw )
import Control.Monad ( forM_ )
import Data.Hashable
import Data.HashMap.Strict ( HashMap )
import qualified Data.HashMap.Strict as HM
import Data.HashSet ( HashSet )
import qualified Data.HashSet as HS
import Data.List ( elemIndex )
import Data.Maybe ( fromMaybe, mapMaybe )
import Data.Monoid

import Database.Datalog

import LLVM.Analysis
import LLVM.Analysis.AccessPath
import LLVM.Analysis.ClassHierarchy
import LLVM.Analysis.PointsTo

-- | This isn't a true points-to analysis because it is an
-- under-approximation.  However, that is sufficient for this library.
instance PointsToAnalysis IndirectCallSummary where
  mayAlias _ _ _ = True
  pointsTo = indirectCallInitializers
  resolveIndirectCall = indirectCallTargets

data CallSummary = ArgumentPosition Function Int
                   -- ^ For describing call argument positions and
                   -- formal positions
                 | Path AbstractAccessPath
                   -- ^ Paths that are assigned to
                 | Target Value
                 deriving (Eq, Ord, Show)

instance Hashable CallSummary where
  hash (ArgumentPosition f i) = 1 `combine` hash f `combine` hash i
  hash (Path p) = 2 `combine` hash p
  hash (Target f) = 3 `combine` hash f

data IndirectCallSummary =
  ICS { summaryTargets :: HashMap AbstractAccessPath (HashSet Value)
      , resolverCHA :: CHA
      }

instance Show IndirectCallSummary where
  show = show . summaryTargets

indirectCallInitializers :: IndirectCallSummary -> Value -> [Value]
indirectCallInitializers s v =
  case valueContent' v of
    InstructionC i -> fromMaybe [] $ do
      accPath <- accessPath i
      let absPath = abstractAccessPath accPath
      return $! indirectCallLookup s absPath
    _ -> []

{-# NOINLINE indirectCallLookup #-}
indirectCallLookup :: IndirectCallSummary -> AbstractAccessPath -> [Value]
indirectCallLookup s = HS.toList . absPathLookup s

-- | Resolve the targets of an indirect call instruction.  This works
-- with both C++ virtual function dispatch and some other common
-- function pointer call patterns.  It is unsound and incomplete.
--
-- FIXME: Make this capable of returning external functions...
-- expected value is low.
indirectCallTargets :: IndirectCallSummary -> Instruction -> [Function]
indirectCallTargets ics i =
  case resolveVirtualCallee (resolverCHA ics) i of
    Just fs -> fs
    Nothing ->
      case i of
        CallInst { callFunction = f } ->
          mapMaybe toFunction $ indirectCallInitializers ics f
        InvokeInst { invokeFunction = f } ->
          mapMaybe toFunction $ indirectCallInitializers ics f
        _ -> []
  where
    toFunction v =
      case valueContent' v of
        FunctionC f -> Just f
        _ -> Nothing

-- | This is the datalog program to compute a simple transitive
-- closure (and unify function actual arguments with formals).  Note
-- that it can't be as polymorphic as certain other datalog functions
-- since it takes no arguments.
pathQuery :: QueryBuilder (Either DatalogError) CallSummary (Query CallSummary)
pathQuery = do
  fptrToField <- relationPredicateFromName "fptrToField"
  fptrAsArg <- relationPredicateFromName "fptrAsArg"
  argToField <- relationPredicateFromName "argToField"
  initializes <- inferencePredicate "initializes"

  let f = LogicVar "F"
      p = LogicVar "P"
      pos = LogicVar "POS"

  (initializes, [f, p]) |- [ lit fptrToField [ f, p ] ]
  (initializes, [f, p]) |- [ lit fptrAsArg [ pos, f ]
                           , lit argToField [ pos, p ]
                           ]
  issueQuery initializes [ f, p ]

-- | Look up the initializers for this abstract access path.  The key
-- here is that we get both the initializers we know for this path,
-- along with initializers for *suffixes* of the path.  For example,
-- if the path is a.b.c.d, we also care about initializers for b.c.d
-- (and c.d).  The recursive walk is in the reducedPathResults
-- segment.
absPathLookup :: IndirectCallSummary -> AbstractAccessPath -> HashSet Value
absPathLookup s@(ICS targets _) absPath =
  pathInits `HS.union` reducedPathResults
  where
    pathInits = HM.lookupDefault mempty absPath targets
    reducedPathResults =
      case reduceAccessPath absPath of
        Nothing -> mempty
        Just rpath -> absPathLookup s rpath

-- | Run the initializer analysis: a cheap pass to identify a subset
-- of possible function pointers that object fields can point to.
{-# NOINLINE identifyIndirectCallTargets #-}
identifyIndirectCallTargets :: Module -> IndirectCallSummary
identifyIndirectCallTargets m = ICS targets (runCHA m)
  where
    facts = either throw id $ do
      db <- buildDatabase m
      queryDatabase db pathQuery
    targets = foldr addTarget mempty facts
    addTarget [Target f, Path p] = HM.insertWith HS.union p (HS.singleton f)
    addTarget _ = error "identifyIndirectCallTargets: database schema mismatch"


buildDatabase :: Module -> Either DatalogError (Database CallSummary)
buildDatabase m = makeDatabase $ do
  fptrToField <- addRelation "fptrToField" 2
  fptrAsArg <- addRelation "fptrAsArg" 2
  argToField <- addRelation "argToField" 2
  mapM_ (factsForGlobal fptrToField) (moduleGlobalVariables m)
  let f = mapM_ (factsForInstruction fptrToField fptrAsArg argToField) . functionInstructions
  mapM_ f (moduleDefinedFunctions m)

-- | Collect facts from global variable initializers.  It currently
-- only handles initializers assigned to global function pointers and
-- global structure initializers.  It does not yet handle nested
-- global initializers.
factsForGlobal :: (Failure DatalogError m)
                  => Relation
                  -> GlobalVariable
                  -> DatabaseBuilder m CallSummary ()
factsForGlobal _ GlobalVariable { globalVariableInitializer = Nothing } = return ()
factsForGlobal fptrToField gv@GlobalVariable { globalVariableInitializer = Just i } =
  case valueContent' i of
    FunctionC f -> addPlainInitializer (toValue f)
    ExternalFunctionC f -> addPlainInitializer (toValue f)
    ConstantC (ConstantStruct _ _ is) ->
      forM_ (zip [0..] is) $ \(idx, initializer) ->
        case valueContent' initializer of
          FunctionC f -> addAggregateInitializer idx (toValue f)
          ExternalFunctionC f -> addAggregateInitializer idx (toValue f)
          _ -> return ()
    _ -> return ()
  where
    addPlainInitializer v =
      let bt = valueType gv
          cs = [AccessDeref]
          p = AbstractAccessPath bt bt cs
      in assertFact fptrToField [ Target v, Path p ]
    addAggregateInitializer idx v =
      let bt = valueType gv
          et = TypePointer (TypePointer (valueType v) 0) 0
          cs = [AccessDeref, AccessField idx]
          p = AbstractAccessPath bt et cs
      in assertFact fptrToField [ Target v, Path p]

-- | Record initializers provided by assignments and function calls in
-- the actual code.
factsForInstruction :: (Failure DatalogError m)
                       => Relation
                       -> Relation
                       -> Relation
                       -> Instruction
                       -> DatabaseBuilder m CallSummary ()
factsForInstruction fptrToField fptrAsArg argToField i =
  case i of
    StoreInst { storeValue = sv, storeAddress = sa } ->
      case valueContent' sv of
        FunctionC f -> addStoredFunc (toValue f)
        ExternalFunctionC ef -> addStoredFunc (toValue ef)
        ArgumentC a ->
          case accessPath i of
            Nothing -> return ()
            Just accPath -> do
              let f = argumentFunction a
                  Just ix = elemIndex a (functionParameters f)
                  absPath = abstractAccessPath accPath
              addSubFacts (\p -> assertFact argToField [ArgumentPosition f ix, Path p]) absPath
        _ -> return ()
    CallInst { callFunction = (valueContent' -> FunctionC f)
             , callArguments = args
             } ->
      mapM_ (argPosFacts f) (zip [0..] (map fst args))
    InvokeInst { invokeFunction = (valueContent' -> FunctionC f)
               , invokeArguments = args
               } ->
      mapM_ (argPosFacts f) (zip [0..] (map fst args))
    _ -> return ()
  where
    addSubFacts func p = do
      _ <- func p
      case reduceAccessPath p of
        Nothing -> return ()
        Just p' -> addSubFacts func p'

    addStoredFunc v =
      case accessPath i of
        Nothing -> return ()
        Just accPath -> do
          let absPath = abstractAccessPath accPath
          addSubFacts (\p -> assertFact fptrToField [Target v, Path p]) absPath

    argPosFacts f (ix, val) =
      case valueContent' val of
        FunctionC fptr ->
          assertFact fptrAsArg [ ArgumentPosition f ix, Target (toValue fptr) ]
        ExternalFunctionC fptr ->
          assertFact fptrAsArg [ ArgumentPosition f ix, Target (toValue fptr) ]
        _ -> return ()
