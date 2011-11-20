{-# LANGUAGE ViewPatterns #-}
module Foreign.Inference.Array (
  ArrayParamSummary,
  identifyArrays
  ) where

import Data.Map ( Map )
import qualified Data.Map as M
import Data.Maybe ( mapMaybe )
import qualified Data.Set as S

import Data.LLVM
import Data.LLVM.CallGraph
import Data.LLVM.Analysis.CallGraphSCCTraversal
import Data.LLVM.Analysis.PointsTo

type ArrayParamSummary = Map (String, String) Int

identifyArrays :: (PointsToAnalysis pta) => CallGraph -> pta -> ArrayParamSummary
identifyArrays cg pta = callGraphSCCTraversal cg (arrayAnalysis pta) M.empty

arrayAnalysis :: (PointsToAnalysis pta) => pta
                 -> Function
                 -> ArrayParamSummary
                 -> ArrayParamSummary
arrayAnalysis pta f summary =
  M.foldlWithKey' (traceFromBases pta f baseResultMap) summary baseResultMap
  where
    insts = concatMap basicBlockInstructions (functionBody f)
    basesAndOffsets = mapMaybe isArrayDeref insts
    baseResultMap = foldr addDeref M.empty basesAndOffsets
    addDeref (load, base, offsets) acc = M.insert base (load, offsets) acc

traceFromBases :: PointsToAnalysis pta
                  => pta
                  -> Function
                  -> Map Value (Value, [Value])
                  -> ArrayParamSummary
                  -> Value
                  -> (Value, [Value])
                  -> ArrayParamSummary
traceFromBases pta f baseResultMap summary base (result, _) =
  case argumentsForBase of
    [] -> summary
    args ->
      let depth = traceBackwards baseResultMap result 1
      in foldr (addToSummary f depth) summary args
  where
    argumentForBase v = case valueContent v of
      ArgumentC a -> if argumentFunction a == f then Just a else Nothing
      _ -> Nothing
    argumentsForBase = mapMaybe argumentForBase $ S.toList (pointsToValues pta base)

addToSummary :: Function -> Int -> Argument -> ArrayParamSummary -> ArrayParamSummary
addToSummary f depth arg summ =
  M.insert (show (functionName f), show (argumentName arg)) depth summ

traceBackwards :: Map Value (Value, [Value]) -> Value -> Int -> Int
traceBackwards baseResultMap result depth =
  -- Is the current result used as the base of an indexing operation?
  -- If so, that adds a level of array wrapping.
  case M.lookup result baseResultMap of
    Nothing -> depth
    Just (result', _) -> traceBackwards baseResultMap result' (depth + 1)

isArrayDeref :: Instruction -> Maybe (Value, Value, [Value])
isArrayDeref inst = case valueContent inst of
  InstructionC LoadInst { loadAddress = (valueContent ->
     InstructionC GetElementPtrInst { getElementPtrValue = base
                                    , getElementPtrIndices = idxs
                                    })} -> Just (Value inst, base, idxs)
  _ -> Nothing