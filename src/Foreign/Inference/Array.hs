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
import Data.LLVM.Analysis.Escape

import Text.Printf
import Debug.Trace
debug = flip trace

type ArrayParamSummary = Map (String, String) Int

identifyArrays :: CallGraph -> EscapeResult -> ArrayParamSummary
identifyArrays cg er = callGraphSCCTraversal cg (arrayAnalysis er) M.empty

arrayAnalysis :: EscapeResult
                 -> Function
                 -> ArrayParamSummary
                 -> ArrayParamSummary
arrayAnalysis er f summary =
  M.foldlWithKey' (traceFromBases f baseResultMap) summary baseResultMap -- `debug` show baseResultMap
  where
    insts = concatMap basicBlockInstructions (functionBody f)
    basesAndOffsets = mapMaybe (isArrayDeref er) insts
    baseResultMap = foldr addDeref M.empty basesAndOffsets
    addDeref (load, base, offsets, eg) acc = M.insert base (load, offsets, eg) acc

traceFromBases :: Function
                  -> Map Value (Value, [Value], EscapeGraph)
                  -> ArrayParamSummary
                  -> Value
                  -> (Value, [Value], EscapeGraph)
                  -> ArrayParamSummary
traceFromBases f baseResultMap summary base (result, _, eg) =
  case argumentsForBase of
    [] -> summary
    args ->
      let depth = traceBackwards baseResultMap result 1
      in foldr (addToSummary f depth) summary args
  where
    argumentForBase v = case valueContent v of
      ArgumentC a -> if argumentFunction a == f then Just a else Nothing
      _ -> Nothing
    ptNode = case valueContent base of
      InstructionC LoadInst { loadAddress = la } -> la
      ArgumentC a -> Value a
    baseAliases = S.map escapeNodeValue $ localPointsTo eg ptNode `debug` show ptNode
    argumentsForBase = mapMaybe argumentForBase $ S.toList baseAliases `debug` show baseAliases



addToSummary :: Function -> Int -> Argument -> ArrayParamSummary -> ArrayParamSummary
addToSummary f depth arg summ =
  M.insert (show (functionName f), show (argumentName arg)) depth summ

traceBackwards :: Map Value (Value, [Value], EscapeGraph) -> Value -> Int -> Int
traceBackwards baseResultMap result depth =
  -- Is the current result used as the base of an indexing operation?
  -- If so, that adds a level of array wrapping.
  case M.lookup result baseResultMap of
    Nothing -> depth
    Just (result', _, _) -> traceBackwards baseResultMap result' (depth + 1)

isArrayDeref :: EscapeResult -> Instruction -> Maybe (Value, Value, [Value], EscapeGraph)
isArrayDeref er inst = case valueContent inst of
  InstructionC LoadInst { loadAddress = (valueContent ->
     InstructionC GetElementPtrInst { getElementPtrValue = base
                                    , getElementPtrIndices = idxs
                                    })} -> Just (Value inst, base, idxs, escapeGraphAtLocation er inst)
  _ -> Nothing