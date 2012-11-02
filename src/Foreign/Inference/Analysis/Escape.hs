{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE OverloadedStrings, FlexibleContexts, RankNTypes #-}
{-# LANGUAGE DeriveGeneric, ViewPatterns, TemplateHaskell #-}
module Foreign.Inference.Analysis.Escape (
  EscapeSummary,
  identifyEscapes,
  instructionEscapes,
  instructionEscapesWith,

  -- * Testing
  EscapeClass(..),
  escapeResultToTestFormat,
  -- escapeUseGraphs,
  -- useGraphvizRepr
  ) where

import GHC.Generics ( Generic )

import Control.DeepSeq
import Control.DeepSeq.Generics ( genericRnf )
import Control.Lens ( Simple, (^.), (%~), (.~), makeLenses )
import Control.Monad.Writer ( runWriter )
import qualified Data.Foldable as F
import Data.Hashable
import Data.HashMap.Strict ( HashMap )
import qualified Data.HashMap.Strict as HM
import Data.List ( mapAccumR )
import Data.Map ( Map )
import qualified Data.Map as M
import Data.Maybe ( fromMaybe, mapMaybe )
import Data.Set ( Set )
import qualified Data.Set as S
import Data.Monoid
import Text.Printf

import LLVM.Analysis
import LLVM.Analysis.AccessPath
import LLVM.Analysis.CallGraphSCCTraversal

import Constraints.Set.Solver

import Foreign.Inference.Diagnostics ( HasDiagnostics(..), Diagnostics )
import Foreign.Inference.Interface
import Foreign.Inference.Internal.FlattenValue
import Foreign.Inference.Analysis.IndirectCallResolver

-- import System.IO.Unsafe
-- import Text.Printf
-- import Debug.Trace
-- debug = flip trace

-- | The ways a value can escape from a function
data EscapeClass = DirectEscape
                 | BrokenContractEscape
                 | IndirectEscape
                 | ArgumentEscape !Int -- ^ Index escaped into
                 deriving (Eq, Ord, Read, Show)

instance Hashable EscapeClass where
  hash DirectEscape = 76
  hash BrokenContractEscape = 699
  hash IndirectEscape = 5
  hash (ArgumentEscape i) = 77997 `combine` hash i

instance NFData EscapeClass

data ArgumentDescriptor = ArgumentDescriptor Function Int
                        deriving (Eq, Ord, Show, Generic)

instance NFData ArgumentDescriptor where
  rnf = genericRnf

data Constructor = Sink { sinkClass :: EscapeClass
                        , sinkWitness :: Instruction
                        , sinkIntoArgument :: Maybe ArgumentDescriptor
                        }
                 deriving (Eq, Ord, Show, Generic)

data Var = Location !Value
         | FieldSource { fieldSourceArgument :: !Argument
                       , fieldSourcePath :: AbstractAccessPath
                       }
         deriving (Eq, Ord, Show, Generic)

type SetExp = SetExpression Var Constructor
type ValueFlowGraph = SolvedSystem Var Constructor

data EscapeGraph = EscapeGraph {
  escapeGraphFieldSourceMap :: HashMap Argument [AbstractAccessPath],
  escapeVFG :: ValueFlowGraph
  } deriving (Eq, Generic)

instance NFData EscapeGraph

-- | The monad in which we construct the value flow graph
-- type GraphBuilder = State GraphState

data EscapeSummary =
  EscapeSummary { _escapeGraph :: HashMap Function EscapeGraph
                , _escapeArguments :: HashMap Argument (EscapeClass, Instruction)
                , _escapeFields :: HashMap Argument (Set (EscapeClass, AbstractAccessPath, Instruction))
                , _escapeIntoArguments :: HashMap Argument (EscapeClass, Function, Int)
                , _escapeDiagnostics :: Diagnostics
                }
  deriving (Generic)

$(makeLenses ''EscapeSummary)

instance Show EscapeSummary where
  show (EscapeSummary _ ea ef ei _) = show ea ++ "/" ++ show ef ++ "/" ++ show ei

instance Eq EscapeSummary where
  (EscapeSummary g1 ea1 ef1 ei1 _) == (EscapeSummary g2 ea2 ef2 ei2 _) =
    g1 == g2 && ea1 == ea2 && ef1 == ef2 && ei1 == ei2

emptySummary :: EscapeSummary
emptySummary = EscapeSummary mempty mempty mempty mempty mempty

instance Monoid EscapeSummary where
  mempty = emptySummary
  mappend (EscapeSummary g1 as1 was1 ei1 d1) (EscapeSummary g2 as2 was2 ei2 d2) =
    EscapeSummary { _escapeGraph = HM.union g1 g2
                  , _escapeArguments = HM.union as1 as2
                  , _escapeFields = HM.union was1 was2
                  , _escapeIntoArguments = HM.union ei1 ei2
                  , _escapeDiagnostics = d1 `mappend` d2
                  }

instance NFData EscapeSummary where
  rnf = genericRnf

instance HasDiagnostics EscapeSummary where
  diagnosticLens = escapeDiagnostics

instance SummarizeModule EscapeSummary where
  summarizeFunction _ _ = []
  summarizeArgument = summarizeEscapeArgument

-- | This is the underlying bottom-up analysis to identify which
-- arguments escape.  It builds an EscapeGraph for the function
-- (incorporating information from other functions that have already
-- been analyzed) and then checks to see which arguments escape using
-- that graph.
identifyEscapes :: (FuncLike funcLike, HasFunction funcLike)
                   => DependencySummary
                   -> IndirectCallSummary
                   -> Simple Lens compositeSummary EscapeSummary
                   -> ComposableAnalysis compositeSummary funcLike
identifyEscapes ds ics lns =
  composableAnalysisM runner escapeWrapper lns
  where
    escapeWrapper funcLike s = do
      let f = getFunction funcLike
          g = buildValueFlowGraph ics ds s (functionInstructions f)
          s' = foldr (summarizeArgumentEscapes g) s (functionParameters f)
      return $ (escapeGraph %~ HM.insert f g) s'

    runner a =
      let (e, diags) = runWriter a
      in (escapeDiagnostics .~ diags) e
{-
    extSumm ef ix =
      -- FIXME: Switch the builder to be a StateT so we can let this
      -- monadic extsumm record missing summaries
      case lookupArgumentSummary ds (undefined :: EscapeSummary) ef ix of
        Nothing -> True --  do
          -- let msg = "Missing summary for " ++ show (externalFunctionName ef)
          -- emitWarning Nothing "EscapeAnalysis" msg
          -- return True
        Just annots -> PAEscape `elem` annots
-}

-- | A generalization of 'instructionEscapes'.  The first argument is
-- a predicate that returns True if the input Instruction (which is a
-- sink) should be excluded from the reachability search of the value
-- flow graph.
--
-- The intended use of this variant is to issue escape queries for
-- instructions that are known to escape via some desired means (e.g.,
-- an out parameter) and to determine if they also escape via some
-- other means.  In that case, the @ignore@ predicate should return
-- True for the store instruction that created the known escape.
instructionEscapesWith :: (Instruction -> Bool)
                          -> Instruction
                          -> EscapeSummary
                          -> Maybe Instruction
instructionEscapesWith = instructionEscapeCore

-- | Returns the instruction (if any) that causes the input
-- instruction to escape.  This does *not* cover WillEscape at all.
instructionEscapes :: Instruction -> EscapeSummary -> Maybe Instruction
instructionEscapes = instructionEscapeCore (const False)

-- | This is shared code for all of the instruction escape queries.
--
-- Most of the description is on 'instructionEscapesWith'
instructionEscapeCore :: (Instruction -> Bool)
                         -> Instruction
                         -> EscapeSummary
                         -> Maybe Instruction
instructionEscapeCore ignorePred i (EscapeSummary egs _ _ _ _) = do
  f <- instructionFunction i
  EscapeGraph _ eg <- HM.lookup f egs
  ts@(_:_) <- leastSolution eg (Location (toValue i))
  let sinks = map toSink ts
      sinks' = filter (not . ignorePred . sinkWitness) sinks
  case sinks' of
    [] -> Nothing
    s:_ -> return (sinkWitness s)

{-
entireArgumentEscapes :: EscapeGraph -> Argument -> EscapeSummary -> Maybe EscapeSummary
entireArgumentEscapes (EscapeGraph _ eg) a s = do
  ts@(_:_) <- leastSolution eg (Location (toValue a))
  let sink:_ = map toSink ts
  return $ (escapeArguments %~ HM.insert a (sinkClass sink, sinkWitness sink)) s
-}

  -- do
  -- ln <- HM.lookup (toValue i) m
  -- let reached = reachableSinks eg (unlabelNode ln) g ignorePred
  -- case filter (not . allocaSink) reached of
  --   [] -> Nothing
  --   (Sink _ w _) : _ -> return w
  --   _ -> error "Non-sink in reachableSinks result 1"
  -- where
  --   Just f = instructionFunction i
  --   errMsg = error ("Missing summary for function " ++ show (functionName f))
  --   eg@(EscapeGraph m _ g) = HM.lookupDefault errMsg f egs

summarizeEscapeArgument :: Argument -> EscapeSummary -> [(ParamAnnotation, [Witness])]
summarizeEscapeArgument a er =
  case HM.lookup a (er ^. escapeArguments) of
    Nothing -> []
    Just (DirectEscape, w@RetInst {}) -> [(PAWillEscape, [Witness w "ret"])]
    Just (t, w@StoreInst {}) -> [(tagToAnnot t, [Witness w "store"])]
    Just (t, w@CallInst {}) -> [(tagToAnnot t, [Witness w "call"])]
    Just (t, w@InvokeInst {}) -> [(tagToAnnot t, [Witness w "call"])]
    Just (t, w) -> [(tagToAnnot t, [Witness w "access"])]
  where
    tagToAnnot t =
      case t of
        DirectEscape -> PAEscape
        IndirectEscape -> PAFptrEscape
        BrokenContractEscape -> PAContractEscape
        ArgumentEscape ix -> PAArgEscape ix

takeFirst :: a -> [Maybe a] -> a
takeFirst def [] = def
takeFirst def (act:rest) =
  case act of
    Nothing -> takeFirst def rest
    Just thing -> thing

summarizeArgumentEscapes :: EscapeGraph -> Argument -> EscapeSummary -> EscapeSummary
summarizeArgumentEscapes eg a s =
  takeFirst s [ entireArgumentEscapes eg a s
              , argumentFieldsEscape eg a s
              ]

toSink :: SetExp -> Constructor
toSink (ConstructedTerm e _ []) = e
toSink e = error ("Foreign.Inference.Analysis.Escape.toSink: Unexpected non-constructed term: " ++ show e)

entireArgumentEscapes :: EscapeGraph -> Argument -> EscapeSummary -> Maybe EscapeSummary
entireArgumentEscapes (EscapeGraph _ eg) a s = do
  ts@(_:_) <- leastSolution eg (Location (toValue a))
  let sink:_ = map toSink ts
  return $ (escapeArguments %~ HM.insert a (sinkClass sink, sinkWitness sink)) s

argumentFieldsEscape :: EscapeGraph -> Argument -> EscapeSummary -> Maybe EscapeSummary
argumentFieldsEscape (EscapeGraph fields eg) a s = do
  fieldPaths <- HM.lookup a fields
  return $ foldr fieldEscapes s fieldPaths
  where
    fieldEscapes fldPath acc = fromMaybe acc $ do
      ts@(_:_) <- leastSolution eg (FieldSource a fldPath)
      let sink:_ = map toSink ts
          entry = S.singleton (sinkClass sink, fldPath, sinkWitness sink)
      return $ (escapeFields %~ HM.insertWith S.union a entry) acc

-- | A helper to abstract the pointer type tests.  If the value @v@ is
-- not a pointer, return @defVal@.  Otherwise, return @isPtrVal@.
-- This helps remove a level of nested (and repetitive) pattern
-- matching.
ifPointer :: IsValue v => v -> a -> a -> a
ifPointer v defVal isPtrVal =
  case valueType v of
    TypePointer _ _ -> isPtrVal
    _ -> defVal

buildValueFlowGraph :: IndirectCallSummary
                       -> DependencySummary
                       -> EscapeSummary
                       -> [Instruction]
                       -> EscapeGraph
buildValueFlowGraph ics ds summ is =
  EscapeGraph { escapeGraphFieldSourceMap = fieldSrcs
              , escapeVFG = sys
              }
  where
    (inclusionSystem, fieldSrcs) = foldr addInclusion ([], mempty) is
    Just sys = solveSystem (constraintSystem inclusionSystem)

    sinkExp klass witness argDesc = atom (Sink klass witness argDesc)
    setExpFor v =
      case valueContent' v of
        InstructionC i@GetElementPtrInst { } ->
          case argumentBasedField i of
            Nothing -> setVariable (Location (stripBitcasts v))
            Just (a, aap) -> setVariable (FieldSource a aap)
        InstructionC i@LoadInst { } ->
          case argumentBasedField i of
            Nothing -> setVariable (Location (stripBitcasts v))
            Just (a, aap) -> setVariable (FieldSource a aap)
        _ -> setVariable (Location (stripBitcasts v))

    addInclusion :: Instruction
                    -> ([Inclusion Var Constructor], HashMap Argument [AbstractAccessPath])
                    -> ([Inclusion Var Constructor], HashMap Argument [AbstractAccessPath])
    addInclusion i acc@(incs, fsrcs) =
      case i of
        RetInst { retInstValue = Just (valueContent' -> rv) } ->
          let s = sinkExp DirectEscape i Nothing
              c = s <=! setExpFor rv
          in (c : incs, fsrcs)
        -- If this is a load of an argument field, we need to make it
        -- into a FieldSource and see what happens to it later.
        -- Record the argument/access path in a map somewhere for
        -- later lookup (otherwise we can't find the variable)
        GetElementPtrInst {} ->
          case argumentBasedField i of
            Just (a, aap) ->
              let c = setExpFor (toValue i) <=! setVariable (FieldSource a aap)
                  srcs' = HM.insertWith (++) a [aap] fsrcs
              in (c : incs, srcs')
            Nothing -> acc
        LoadInst { loadAddress = la } ->
          ifPointer i acc $
            case argumentBasedField i of
              Just _ ->
                let c = setExpFor (toValue i) <=! setExpFor la
                in (c : incs, fsrcs)
              _ -> acc
        StoreInst { storeAddress = sa
                  , storeValue = sv
                  }
          | mustEsc ->
            let sinkTag = maybe DirectEscape (ArgumentEscape . argumentIndex) mArg
                s = sinkExp sinkTag i Nothing
                c = s <=! setExpFor sv
            in (c : incs, fsrcs)
          | otherwise ->
              -- May escape later if the alloca escapes
              let c = setExpFor sa <=! setExpFor sv
              in (c : incs, fsrcs)
          where
            (mustEsc, mArg) = mustEscapeLocation sa

        CallInst { callFunction = callee, callArguments = (map (stripBitcasts . fst) -> args) } ->
          addCallConstraints i acc callee args
        InvokeInst { invokeFunction = callee, invokeArguments = (map (stripBitcasts . fst) -> args) } ->
          addCallConstraints i acc callee args
        SelectInst { selectTrueValue = (valueContent' -> tv)
                   , selectFalseValue = (valueContent' -> fv)
                   } ->
          let c1 = setExpFor (toValue i) <=! setExpFor tv
              c2 = setExpFor (toValue i) <=! setExpFor fv
          in (c1 : c2 : incs, fsrcs)
        PhiNode { phiIncomingValues = (map (stripBitcasts . fst) -> ivs) } ->
          let toIncl v = setExpFor (toValue i) <=! setExpFor v
              cs = map toIncl ivs
          in (cs ++ incs, fsrcs)
        _ -> acc

    addCallConstraints callInst (incs, fsrcs) callee args =
      case valueContent' callee of
        FunctionC f ->
          let indexedArgs = zip [0..] args
          in (foldr (addActualConstraint callInst f) incs indexedArgs, fsrcs)
        ExternalFunctionC ef ->
          let indexedArgs = zip [0..] args
          in (foldr (addActualConstraint callInst ef) incs indexedArgs, fsrcs)
        _ ->
          case indirectCallInitializers ics callee of
            -- No targets known; all pointer arguments indirectly escape
            [] -> (foldr (addIndirectEscape callInst) incs args, fsrcs)
            -- We have at least one target; take it as a representative
            (repr:_) ->
              let indexedArgs = zip [0..] args
              in (foldr (addContractEscapes callInst repr) incs indexedArgs, fsrcs)

    argEscapeConstraint callInst etype actual incs =
      -- FIXME; figure out how to use the index in a field escape here
      let s = sinkExp etype callInst Nothing
          c = s <=! setExpFor actual
      in c : incs

    addContractEscapes callInst repr (ix, actual) incs =
      ifPointer actual incs $
        case lookupArgumentSummary ds summ repr ix of
          -- If we don't have a summary for oure representative, treat
          -- it as an indirect call with no known target (we could do
          -- better by looking at the next possible representative, if
          -- any).
          Nothing -> addIndirectEscape callInst actual incs
          Just pannots ->
            case F.find isEscapeAnnot pannots of
              -- If we don't find an escape annotation, we generate a
              -- BrokenContractEscape since the argument will only
              -- escape if the function pointer breaks a contract
              Nothing -> argEscapeConstraint callInst BrokenContractEscape actual incs
              Just PAEscape -> argEscapeConstraint callInst DirectEscape actual incs
              Just PAContractEscape -> argEscapeConstraint callInst BrokenContractEscape actual incs
              Just PAFptrEscape -> argEscapeConstraint callInst IndirectEscape actual incs
              _ -> incs

    addActualConstraint callInst callee (ix, actual) incs =
      fromMaybe incs $ do
        pannots <- lookupArgumentSummary ds summ callee ix
        escAnnot <- F.find isEscapeAnnot pannots
        case escAnnot of
          PAEscape -> return $ argEscapeConstraint callInst DirectEscape actual incs
          PAContractEscape -> return $ argEscapeConstraint callInst BrokenContractEscape actual incs
          PAFptrEscape -> return $ argEscapeConstraint callInst IndirectEscape actual incs
          _ -> Nothing

    addIndirectEscape callInst actual incs =
      ifPointer actual incs $
        argEscapeConstraint callInst IndirectEscape actual incs

isEscapeAnnot :: ParamAnnotation -> Bool
isEscapeAnnot a =
  case a of
    PAEscape -> True
    PAArgEscape _ -> True
    PAContractEscape -> True
    PAFptrEscape -> True
    _ -> False
-- Ignore PAWillEscape for now...


-- Given a GetElementPtrInst, return its base and the path accessed
-- IFF the base was an Argument.
argumentBasedField :: Instruction -> Maybe (Argument, AbstractAccessPath)
argumentBasedField li = do
  accPath <- accessPath li
  case valueContent' (accessPathBaseValue accPath) of
    ArgumentC a -> return (a, abstractAccessPath accPath)
    _ -> Nothing

mustEscapeLocation :: Value -> (Bool, Maybe Argument)
mustEscapeLocation = snd . go mempty
  where
    go visited v
      | S.member v visited = (visited, (False, Nothing))
      | otherwise =
        case valueContent' v of
          GlobalVariableC _ -> (visited', (True, Nothing))
          ExternalValueC _ -> (visited', (True, Nothing))
          ArgumentC a -> (visited', (True, Just a))
          InstructionC CallInst {} -> (visited', (True, Nothing))
          InstructionC InvokeInst {} -> (visited', (True, Nothing))
          InstructionC LoadInst { loadAddress = la } ->
            go visited' la
          InstructionC GetElementPtrInst { getElementPtrValue = base } ->
            go visited' base
          InstructionC SelectInst { } ->
            let (visited'', pairs) = mapAccumR go visited' (flattenValue v)
                argVal = mconcat $ map (First . snd) pairs
            in (visited'', (any fst pairs, getFirst argVal))
          InstructionC PhiNode {} ->
            let (visited'', pairs) = mapAccumR go visited' (flattenValue v)
                argVal = mconcat $ map (First . snd) pairs
            in (visited'', (any fst pairs, getFirst argVal))
          _ -> (visited', (False, Nothing))
      where
        visited' = S.insert v visited

argumentIndex :: Argument -> Int
argumentIndex a = ix
  where
    Just (ix, _) = F.find ((==a) . snd) ps
    f = argumentFunction a
    ps = zip [0..] (functionParameters f)

-- Testing

-- | Extract the arguments for each function that escape.  The keys of
-- the map are function names and the set elements are argument names.
-- This format exposes the internal results for testing purposes.
--
-- For actual use in a program, use one of 'functionEscapeArguments',
-- 'functionWillEscapeArguments', or 'instructionEscapes' instead.
escapeResultToTestFormat :: EscapeSummary -> Map String (Set (EscapeClass, String))
escapeResultToTestFormat er =
  M.filter (not . S.null) $ foldr fieldTransform argEscapes (HM.toList fm)
  where
    directEscapes = foldr transform mempty (HM.toList m)
    argEscapes = foldr argTransform directEscapes (HM.toList am)
    m = er ^. escapeArguments
    fm = er ^. escapeFields
    am = er ^. escapeIntoArguments
    argTransform (a, (tag, _, _)) acc =
      let aname = show (argumentName a)
          f = argumentFunction a
          fname = show (functionName f)
      in M.insertWith' S.union fname (S.singleton (tag, aname)) acc
    transform (a, (tag, _)) acc =
      let f = argumentFunction a
          fname = show (functionName f)
          aname = show (argumentName a)
      in M.insertWith' S.union fname (S.singleton (tag, aname)) acc
    fieldTransform (a, fieldsAndInsts) acc =
      let f = argumentFunction a
          fname = show (functionName f)
          aname = show (argumentName a)
          tagsAndFields = S.toList $ S.map (\(tag, fld, _) -> (tag, fld)) fieldsAndInsts
          newEntries = S.fromList $ mapMaybe (toFieldRef aname) tagsAndFields
      in M.insertWith' S.union fname newEntries acc
    toFieldRef aname (tag, fld) =
      case abstractAccessPathComponents fld of
        [AccessDeref, AccessField ix] -> Just $ (tag, printf "%s.<%d>" aname ix)
        _ -> Nothing
