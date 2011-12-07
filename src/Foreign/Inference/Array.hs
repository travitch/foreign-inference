{-# LANGUAGE ViewPatterns #-}
-- | This module defines the Array Analysis from the PLDI 2009 paper.
--
-- The analysis identifies which pointer parameters of a function are
-- used as arrays in that function (or any callees).  The analysis is
-- flow insensitive and works by examining chains of GetElementPtr and
-- Load instructions to reconstruct the shape of arrays that are
-- accessed.
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

-- | The analysis to generate array parameter summaries for an entire
-- Module (via the CallGraph).  Example usage:
--
-- > let pta = runPointsToAnalysis m
-- >     cg = mkCallGraph m pta []
-- >     er = runEscapeAnalysis m cg
-- > in identifyArrays cg er
identifyArrays :: CallGraph -> EscapeResult -> ArrayParamSummary
identifyArrays cg er = callGraphSCCTraversal cg (arrayAnalysis er) M.empty

-- | The summarization function - add a summary for the current
-- Function to the current summary.  This function collects all of the
-- base+offset pairs and then uses @traceFromBases@ to reconstruct
-- them.
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

-- | Examine a GetElementPtr instruction result.  If the base is an
-- argument, trace its access structure (using the @baseResultMap@ via
-- @traceBackwards@) and record the dimensions in the summary.
--
-- Otherwise, just pass the summary along and try to find the next
-- access.
traceFromBases :: Function
                  -> Map Value (Value, [Value], EscapeGraph)
                  -> ArrayParamSummary
                  -> Value
                  -> (Value, [Value], EscapeGraph)
                  -> ArrayParamSummary
traceFromBases f baseResultMap summary base (result, _, eg) =
  case argumentsForValue eg base of
    [] -> summary
    args ->
      let depth = traceBackwards baseResultMap result 1
      in foldr (addToSummary f depth) summary args

-- | Figure out which arguments, if any, correspond to the given value
-- in the points-to escape graph (flow-sensitive points-to
-- information).
--
-- This function makes a best effort to handle struct references.
argumentsForValue :: EscapeGraph -> Value -> [Argument]
argumentsForValue eg v =
  mapMaybe extractArgument baseAliases `debug` show baseAliases
  where
  ptNode = case valueContent v of
    InstructionC AllocaInst {} -> v
    InstructionC LoadInst { loadAddress =
      (valueContent' -> InstructionC i@GetElementPtrInst {})} -> Value i `debug` "Base is load gep"
    InstructionC LoadInst { loadAddress = la } -> la
    GlobalVariableC g -> Value g
    ExternalValueC e -> Value e
    ArgumentC a -> Value a
  baseAliases = case valueInGraph eg ptNode of
    False -> []
    True -> map escapeNodeValue $ S.toList $ localPointsTo eg ptNode  `debug` printf "Node %d == %s" (valueUniqueId ptNode) (show ptNode )
  -- | If the given base value is an Argument, convert it to an Argument
  -- and return it.  Otherwise, return Nothing.x
  extractArgument :: IsValue a => a -> Maybe Argument
  extractArgument val = case valueContent val of
    ArgumentC a -> Just a
    _ -> Nothing

-- | Update the summary for an argument with a depth
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

-- | FIXME: Ignore GEPs that are struct references (constant zero base
-- with a second or higher index).
isArrayDeref :: EscapeResult -> Instruction -> Maybe (Value, Value, [Value], EscapeGraph)
isArrayDeref er inst = case valueContent inst of
  InstructionC LoadInst { loadAddress = (valueContent ->
     InstructionC GetElementPtrInst { getElementPtrValue = base
                                    , getElementPtrIndices = idxs
                                    })} -> Just (Value inst, base, idxs, escapeGraphAtLocation er inst)
  _ -> Nothing