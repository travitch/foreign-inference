{-# LANGUAGE ViewPatterns #-}
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
module Foreign.Inference.Analysis.SingleInitializer (
  SingleInitializerSummary,
  identifySingleInitializers,
  singleInitializer,
  indirectCallInitializer
  ) where

import Data.List ( elemIndex, find, foldl', intercalate )
import Data.List.Ordered ( union )
import Data.Map ( Map )
import qualified Data.Map as M
import Data.Maybe ( mapMaybe )
import Data.Monoid

import LLVM.Analysis
import LLVM.Analysis.AccessPath
import LLVM.Analysis.ClassHierarchy
import LLVM.Analysis.PointsTo

-- import Text.Printf
-- import Debug.Trace
-- debug = flip trace

-- FIXME Rename to IndirectCallResolver

-- | This isn't a true points-to analysis because it is an
-- under-approximation.  However, that is sufficient for this library.
instance PointsToAnalysis SingleInitializerSummary where
  mayAlias _ _ _ = True
  pointsTo = singleInitializer
  resolveIndirectCall = indirectCallInitializer

data SingleInitializerSummary =
  SIS { abstractPathInitializers :: !(Map AbstractAccessPath [Value])
        -- ^ Function initializers assigned to fields of types
      , concreteValueInitializers :: !(Map GlobalVariable [Value])
        -- ^ Explicit values assigned to global variables, either at
        -- initialization time or through a later assignment.
      , argumentInitializers :: !(Map (Function, Int) [Value])
        -- ^ A map of all of the known initializers (Functions or
        -- External functions) passed as the ix'th argument of the
        -- Function that is the key of the map.
      , fieldArgDependencies :: !(Map AbstractAccessPath [(Function, Int)])
      , globalArgDependencies :: !(Map GlobalVariable [(Function, Int)])
      , canonicalTypeMap :: Map Type Type
      , resolverCHA :: CHA
      }

instance Show SingleInitializerSummary where
  show (SIS api cbi _ _ _ _ _) = concat [ "Abstract Path Initializers\n"
                                        , unlines $ map showAPI (M.toList api)
                                        , "\nConcrete Value Initializers\n"
                                        , unlines $ map showCBI (M.toList cbi)
                                        ]
    where
      showAPI (aap, vs) = concat [ " * ", show aap, ": ", intercalate ", " (map (show . valueName) vs)]
      showCBI (gv, vs) = concat [ " * ", show (globalVariableName gv), ": ", intercalate ", " (map (show . valueName) vs)]

emptyInitializerSummary :: Module -> Map GlobalVariable [Value] -> SingleInitializerSummary
emptyInitializerSummary m cvis =
  SIS mempty cvis mempty mempty mempty ctm cha
  where
    ctm = makeCanonicalTypeMap (moduleRetainedTypes m)
    cha = runCHA m

makeCanonicalTypeMap :: [Type] -> Map Type Type
makeCanonicalTypeMap ts =
  foldr canonicalize mempty (M.toList typesByName)
  where
    typesByName = foldr addTypeByName mempty ts
    addTypeByName t m =
      case t of
        TypeStruct _ _ _ ->
          case structTypeToName t of
            Nothing -> m
            Just tn -> M.insertWith' (++) tn [t] m
        _ -> m
    canonicalize (_, gts) acc =
      case find nameHasOneDot gts of
        Nothing -> acc
        Just ctype -> foldr (insertCanonical ctype) acc gts
    insertCanonical ctype t = M.insert t ctype
    -- Struct names with one dot are of the form struct.name -- they
    -- have no numeric suffix.  These are the types we are taking as
    -- canonical
    nameHasOneDot (TypeStruct (Just n) _ _) = length (filter (=='.') n) == 1
    nameHasOneDot _ = False

canonicalizeType :: SingleInitializerSummary -> Type -> Type
canonicalizeType sis ty@(TypeStruct _ _ _) =
  M.findWithDefault ty ty (canonicalTypeMap sis)
canonicalizeType sis (TypePointer t' a) =
  TypePointer (canonicalizeType sis t') a
canonicalizeType sis (TypeFunction r ts v) =
  TypeFunction (canonicalizeType sis r) (map (canonicalizeType sis) ts) v
canonicalizeType _ t = t


-- | Canonicalize types in all abstract access paths.  Computed AAPs
-- in the lookup step will also need to canonicalize.  Just assume
-- that types sharing the same name are all the same and ignore .NNN
-- variants.
--
-- With the canonicalization, initializations from different
-- compilation units can be merged even if the LLVM linker was unable
-- to unify all variants of a type.
--
-- The mangled types coming from clang are strange and I haven't had time
-- to track down the root cause yet.
canonicalizeAccessPath :: SingleInitializerSummary
                          -> AbstractAccessPath
                          -> AbstractAccessPath
canonicalizeAccessPath s (AbstractAccessPath bt et cs) =
  AbstractAccessPath { abstractAccessPathBaseType = canonicalizeType s bt
                     , abstractAccessPathEndType = canonicalizeType s et
                     , abstractAccessPathComponents = cs
                     }

singleInitializer :: SingleInitializerSummary -> Value -> [Value]
singleInitializer s v =
  case valueContent' v of
    InstructionC i -> maybe [] id $ do
      accPath <- accessPath i
      let absPath = abstractAccessPath accPath
          cabsPath = canonicalizeAccessPath s absPath
      case valueContent' (accessPathBaseValue accPath) of
        GlobalVariableC gv@GlobalVariable { globalVariableInitializer = Just initVal } ->
          case followAccessPath cabsPath initVal of
            Nothing -> return $! globalVarLookup s gv
            accPathVal -> fmap return accPathVal
        _ -> return $! absPathLookup s cabsPath
    _ -> []

-- | Resolve the targets of an indirect call instruction.  This works
-- with both C++ virtual function dispatch and some other common
-- function pointer call patterns.  It is unsound and incomplete.
--
-- FIXME: Make this capable of returning external functions...
-- expected value is low.
indirectCallInitializer :: SingleInitializerSummary -> Instruction -> [Function]
indirectCallInitializer sis i =
  case resolveVirtualCallee (resolverCHA sis) i of
    Just fs -> fs
    Nothing ->
      case i of
        CallInst { callFunction = f } ->
          mapMaybe toFunction $ singleInitializer sis f
        InvokeInst { invokeFunction = f } ->
          mapMaybe toFunction $ singleInitializer sis f
        _ -> []
  where
    toFunction v =
      case valueContent' v of
        FunctionC f -> Just f
        _ -> Nothing

-- | Look up the initializers for this abstract access path.  The key
-- here is that we get both the initializers we know for this path,
-- along with initializers for *suffixes* of the path.  For example,
-- if the path is a.b.c.d, we also care about initializers for b.c.d
-- (and c.d).  The recursive walk is in the reducedPathResults
-- segment.
absPathLookup :: SingleInitializerSummary -> AbstractAccessPath -> [Value]
absPathLookup s absPath = storeInits `union` argInits `union` reducedPathResults
  where
    storeInits = M.findWithDefault [] absPath (abstractPathInitializers s)
    argDeps = M.findWithDefault [] absPath (fieldArgDependencies s)
    argInits = concatMap (\x -> M.findWithDefault [] x (argumentInitializers s)) argDeps
    reducedPathResults =
      case reduceAccessPath absPath of
        Nothing -> []
        Just rpath -> absPathLookup s rpath

globalVarLookup :: SingleInitializerSummary -> GlobalVariable -> [Value]
globalVarLookup s gv = concreteInits `union` argInits
  where
    concreteInits = M.findWithDefault [] gv (concreteValueInitializers s)
    argDeps = M.findWithDefault [] gv (globalArgDependencies s)
    argInits = concatMap (\x -> M.findWithDefault [] x (argumentInitializers s)) argDeps

-- | Run the initializer analysis: a cheap pass to identify a subset
-- of possible function pointers that object fields can point to.
identifySingleInitializers :: Module -> SingleInitializerSummary
identifySingleInitializers m =
  foldl' (flip recordInitializers) s0 allInsts
  where
    s0 = emptyInitializerSummary m (M.fromList globalsWithInits)
    allBlocks = concatMap functionBody $ moduleDefinedFunctions m
    allInsts = concatMap basicBlockInstructions allBlocks
    globalsWithInits = foldr extractGlobalsWithInits [] (moduleGlobalVariables m)

extractGlobalsWithInits :: GlobalVariable
                           -> [(GlobalVariable, [Value])]
                           -> [(GlobalVariable, [Value])]
extractGlobalsWithInits gv acc =
  case globalVariableInitializer gv of
    Nothing -> acc
    Just i -> (gv, [i]) : acc

recordInitializers :: Instruction -> SingleInitializerSummary -> SingleInitializerSummary
recordInitializers i s =
  case i of
    StoreInst { storeValue = sv, storeAddress = sa } ->
      case valueContent' sv of
        FunctionC _ -> maybeRecordInitializer i sv sa s
        ExternalFunctionC _ -> maybeRecordInitializer i sv sa s
        ArgumentC a ->
          let f = argumentFunction a
              Just ix = elemIndex a (functionParameters f)
          in recordArgInitializer i f ix sa s
        _ -> s
    CallInst { callFunction = (valueContent' -> FunctionC f)
             , callArguments = args
             } ->
      let ixArgs = zip [0..] $ map fst args
      in foldl' (recordArgFuncInit f) s ixArgs
    InvokeInst { invokeFunction = (valueContent' -> FunctionC f)
               , invokeArguments = args
               } ->
      let ixArgs = zip [0..] $ map fst args
      in foldl' (recordArgFuncInit f) s ixArgs
    _ -> s

-- | If an actual argument has a Function (or ExternalFunction) as its
-- value, record that as a value as associated with the ix'th argument
-- of the callee.
recordArgFuncInit :: Function
                     -> SingleInitializerSummary
                     -> (Int, Value)
                     -> SingleInitializerSummary
recordArgFuncInit f s (ix, arg) =
  case valueContent' arg of
    FunctionC _ ->
      s { argumentInitializers =
             M.insertWith union (f, ix) [arg] (argumentInitializers s)
        }
    ExternalFunctionC _ ->
      s { argumentInitializers =
             M.insertWith union (f, ix) [arg] (argumentInitializers s)
        }
    _ -> s

recordArgInitializer :: Instruction
                        -> Function
                        -> Int
                        -> Value
                        -> SingleInitializerSummary
                        -> SingleInitializerSummary
recordArgInitializer i f ix sa s =
  case valueContent' sa of
    GlobalVariableC gv ->
      s { globalArgDependencies =
             M.insertWith' union gv [(f, ix)] (globalArgDependencies s)
        }
    _ ->
      case accessPath i of
        Nothing -> s
        Just accPath ->
          let absPath = abstractAccessPath accPath
              cabsPath = canonicalizeAccessPath s absPath
          in s { fieldArgDependencies =
                    M.insertWith' union cabsPath [(f, ix)] (fieldArgDependencies s)
               }

-- | Initializers here (sv) are only functions (external or otherwise)
maybeRecordInitializer :: Instruction -> Value -> Value
                          -> SingleInitializerSummary
                          -> SingleInitializerSummary
maybeRecordInitializer i sv sa s =
  case valueContent' sa of
    GlobalVariableC gv ->
      s { concreteValueInitializers =
             M.insertWith' union gv [sv] (concreteValueInitializers s)
        }
    _ ->
      case accessPath i of
        Nothing -> s
        Just accPath ->
          let absPath = abstractAccessPath accPath
              cabsPath = canonicalizeAccessPath s absPath
          in s { abstractPathInitializers =
                    M.insertWith' union cabsPath [sv] (abstractPathInitializers s)
               }
