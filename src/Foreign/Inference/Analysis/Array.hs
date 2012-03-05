{-# LANGUAGE ViewPatterns, TemplateHaskell #-}
-- | This module defines the Array Analysis from the PLDI 2009 paper.
--
-- The analysis identifies which pointer parameters of a function are
-- used as arrays in that function (or any callees).  The analysis is
-- flow insensitive and works by examining chains of GetElementPtr and
-- Load instructions to reconstruct the shape of arrays that are
-- accessed.
module Foreign.Inference.Analysis.Array (
  -- * Interface
  ArraySummary,
  identifyArrays,
  -- * Testing
  arraySummaryToTestFormat
  ) where

import Control.DeepSeq
import Data.List ( foldl' )
import Data.Lens.Common
import Data.Map ( Map )
import qualified Data.Map as M
import FileLocation

import LLVM.Analysis
import LLVM.Analysis.CallGraphSCCTraversal

import Foreign.Inference.AnalysisMonad
import Foreign.Inference.Diagnostics
import Foreign.Inference.Interface
import Foreign.Inference.Internal.FlattenValue

-- import Debug.Trace
-- debug' = flip trace

-- | The real type of the summary (without the wrapper that is exposed
-- to clients).
type SummaryType = Map Argument Int

-- | Summarize the array parameters in the module.  This maps each
-- array argument to its inferred dimensionality.
-- newtype ArraySummary = APS SummaryType
data ArraySummary =
  ArraySummary { arraySummary :: SummaryType
               , arrayDiagnostics :: Diagnostics
               }

instance Eq ArraySummary where
  (ArraySummary s1 _) == (ArraySummary s2 _) = s1 == s2

instance Monoid ArraySummary where
  mempty = ArraySummary M.empty mempty
  mappend (ArraySummary s1 d1) (ArraySummary s2 d2) =
    ArraySummary (M.unionWith max s1 s2) (mappend d1 d2)

instance NFData ArraySummary where
  rnf a@(ArraySummary s d) = d `deepseq` s `deepseq` a `seq` ()

instance HasDiagnostics ArraySummary where
  addDiagnostics s d =
    s { arrayDiagnostics = arrayDiagnostics s `mappend` d }
  getDiagnostics = arrayDiagnostics

instance SummarizeModule ArraySummary where
  summarizeFunction _ _ = []
  summarizeArgument = summarizeArrayArgument

summarizeArrayArgument :: Argument -> ArraySummary -> [(ParamAnnotation, [Witness])]
summarizeArrayArgument a (ArraySummary summ _) =
  case M.lookup a summ of
    Nothing -> []
    Just depth -> [(PAArray depth, [])]

data ArrayData = AD { dependencySummary :: DependencySummary
                    }

type Analysis = AnalysisMonad ArrayData ()

-- | A data type to capture uses of pointers in array contexts.  These
-- are accumulated in one pass over the function and then used to
-- reconstruct the shapes of arrays in the tracing functions.
data PointerUse = IndexOperation Value [Value]
                | CallArgument Int
                deriving (Show)

identifyArrays :: (FuncLike funcLike, HasFunction funcLike)
                  => DependencySummary
                  -> Lens compositeSummary ArraySummary
                  -> ComposableAnalysis compositeSummary funcLike
identifyArrays ds lns =
  composableAnalysisM runner arrayAnalysis lns
  where
    runner a = runAnalysis a readOnlyData ()
    readOnlyData = AD ds

-- | The summarization function - add a summary for the current
-- Function to the current summary.  This function collects all of the
-- base+offset pairs and then uses @traceFromBases@ to reconstruct
-- them.
arrayAnalysis :: (FuncLike funcLike, HasFunction funcLike)
                 => funcLike -> ArraySummary -> Analysis ArraySummary
arrayAnalysis funcLike a@(ArraySummary summary _) = do
  ds <- asks dependencySummary

  let basesAndOffsets = concatMap (isArrayDeref ds summary) insts
      baseResultMap = foldr addDeref M.empty basesAndOffsets
      summary' = M.foldlWithKey' (traceFromBases baseResultMap) summary baseResultMap
  return $! a { arraySummary = summary' }
  where
    f = getFunction funcLike
    insts = concatMap basicBlockInstructions (functionBody f)
    addDeref (base, use) = M.insertWith' (++) base [use]

-- | Examine a GetElementPtr instruction result.  If the base is an
-- argument, trace its access structure (using the @baseResultMap@ via
-- @traceBackwards@) and record the dimensions in the summary.
--
-- Otherwise, just pass the summary along and try to find the next
-- access.
traceFromBases :: Map Value [PointerUse]
                  -> SummaryType
                  -> Value
                  -> [PointerUse]
                  -> SummaryType
traceFromBases baseResultMap summary base uses =
  -- FIXME: This test of argumentness needs to be extended to take
  -- into account PHI nodes (also selects)
  case valueContent' base of
    ArgumentC a ->
      let depth = maximum $ map dispatchTrace uses
      in addToSummary depth a summary
    _ -> summary
  where
    dispatchTrace (IndexOperation result _) =
      traceBackwards baseResultMap result 1
    dispatchTrace (CallArgument depth) = depth

-- | Update the summary for an argument with a depth.
--
-- The function always keeps the *maximum* array depth it discovers
-- (i.e., inserting an array depth of 1 for an argument that is
-- already recorded as having depth 2 will not make any changes to the
-- summary).
addToSummary :: Int -> Argument -> SummaryType -> SummaryType
addToSummary depth arg =
  M.insertWith max arg depth


traceBackwards :: Map Value [PointerUse] -> Value -> Int -> Int
traceBackwards baseResultMap result depth =
  -- Is the current result used as the base of an indexing operation?
  -- If so, that adds a level of array wrapping.
  case M.lookup result baseResultMap of
    Nothing -> depth
    Just uses -> maximum (map dispatchTrace uses)
  where
    dispatchTrace use =
      case use of
        IndexOperation result' _ -> traceBackwards baseResultMap result' (depth + 1)
        CallArgument d -> depth + d

isArrayDeref :: DependencySummary
                -> SummaryType
                -> Instruction
                -> [(Value, PointerUse)]
isArrayDeref ds summ inst = case valueContent' inst of
  InstructionC LoadInst { loadAddress = (valueContent ->
     InstructionC GetElementPtrInst { getElementPtrValue = base
                                    , getElementPtrIndices = idxs
                                    })} ->
    concatMap (buildArrayDeref inst idxs) (flattenValue base)
  InstructionC StoreInst { storeAddress = (valueContent ->
     InstructionC GetElementPtrInst { getElementPtrValue = base
                                    , getElementPtrIndices = idxs
                                    })} ->
    concatMap (buildArrayDeref inst idxs) (flattenValue base)
  InstructionC AtomicCmpXchgInst { atomicCmpXchgPointer = (valueContent ->
    InstructionC GetElementPtrInst { getElementPtrValue = base
                                    , getElementPtrIndices = idxs
                                    })} ->
    concatMap (buildArrayDeref inst idxs) (flattenValue base)
  InstructionC AtomicRMWInst { atomicRMWPointer = (valueContent ->
    InstructionC GetElementPtrInst { getElementPtrValue = base
                                    , getElementPtrIndices = idxs
                                    })} ->
    concatMap (buildArrayDeref inst idxs) (flattenValue base)
  InstructionC CallInst { callFunction = f, callArguments = args } ->
    let indexedArgs = zip [0..] (map fst args)
    in foldl' (collectArrayArgs ds summ f) [] (concatMap expand indexedArgs)
  InstructionC InvokeInst { invokeFunction = f, invokeArguments = args } ->
    let indexedArgs = zip [0..] (map fst args)
    in foldl' (collectArrayArgs ds summ f) [] (concatMap expand indexedArgs)
  _ -> []
  where
    expand (ix, a) = zip (repeat ix) (flattenValue a)

buildArrayDeref :: Instruction -> [Value] -> Value -> [(Value, PointerUse)]
buildArrayDeref inst idxs base =
  case idxs of
    [] -> $err' ("GEP with no indices: " ++ show inst)
    [_] -> [(base, IndexOperation (Value inst) idxs)]
    (valueContent' -> ConstantC ConstantInt { constantIntValue = 0 }) : _ -> []
    _ -> [(base, IndexOperation (Value inst) idxs )]

-- | If the argument is an array (according to either the module
-- summary or the dependency summary), make a CallArgument tag for it.
-- Only bother inspecting direct calls.  Information gained from
-- indirect calls is unreliable since we don't have all possible
-- callees, even with a very powerful points-to analysis.
collectArrayArgs :: DependencySummary -> SummaryType
                    -> Value -> [(Value, PointerUse)] -> (Int, Value)
                    -> [(Value, PointerUse)]
collectArrayArgs ds summ callee lst (ix, arg) =
  case valueContent' callee of
    FunctionC f ->
      let funcArgs = functionParameters f
      in case (ix < length funcArgs, functionIsVararg f) of
        (True, _) -> case M.lookup (funcArgs !! ix) summ of
          Nothing -> lst
          Just depth -> (arg, CallArgument depth) : lst
        -- Args passed as varargs don't give us any information (in general)
        (False, True) -> []
        (False, False) -> $err' ("ArrayAnalysis: argument index out of range: " ++ show (functionName f) ++ " : " ++ show arg)
    -- Look up the ixth argument of the callee in the
    -- DependencySummary and record it if it is tagged with a PAArray
    -- annotation
    ExternalFunctionC e ->
      case lookupArgumentSummary ds e ix of
        Nothing -> lst
        Just annots -> case filter isArrayAnnot annots of
          [] -> lst
          [PAArray depth] -> (arg, CallArgument depth) : lst
          _ -> $(err "This summary should only produce singleton or empty lists")
    _ -> []

isArrayAnnot :: ParamAnnotation -> Bool
isArrayAnnot (PAArray _) = True
isArrayAnnot _ = False


-- Testing

arraySummaryToTestFormat :: ArraySummary -> Map (String, String) Int
arraySummaryToTestFormat (ArraySummary summ _) =
  M.mapKeys argToString summ
  where
    argToString a =
      let f = argumentFunction a
      in (show (functionName f), show (argumentName a))
