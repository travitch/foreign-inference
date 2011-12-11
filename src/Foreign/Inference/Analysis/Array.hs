{-# LANGUAGE ViewPatterns #-}
-- | This module defines the Array Analysis from the PLDI 2009 paper.
--
-- The analysis identifies which pointer parameters of a function are
-- used as arrays in that function (or any callees).  The analysis is
-- flow insensitive and works by examining chains of GetElementPtr and
-- Load instructions to reconstruct the shape of arrays that are
-- accessed.
module Foreign.Inference.Analysis.Array (
  -- * Interface
  ArrayParamSummary,
  identifyArrays,
  -- * Testing
  arraySummaryToTestFormat
  ) where

import Data.Map ( Map )
import qualified Data.Map as M
import Data.Maybe ( mapMaybe )
import qualified Data.Set as S

import Data.LLVM
import Data.LLVM.CallGraph
import Data.LLVM.Analysis.CallGraphSCCTraversal
import Data.LLVM.Analysis.Escape

import Foreign.Inference.Interface
import Foreign.Inference.Internal.ValueArguments

type SummaryType = Map Argument Int

-- | Summarize the array parameters in the module.  This maps each
-- array argument to its inferred dimensionality.
newtype ArrayParamSummary = APS SummaryType

-- | The analysis to generate array parameter summaries for an entire
-- Module (via the CallGraph).  Example usage:
--
-- > let pta = runPointsToAnalysis m
-- >     cg = mkCallGraph m pta []
-- >     er = runEscapeAnalysis m cg
-- > in identifyArrays cg er
identifyArrays :: CallGraph -> EscapeResult -> ArrayParamSummary
identifyArrays cg er = APS $ callGraphSCCTraversal cg (arrayAnalysis er) M.empty

-- | The summarization function - add a summary for the current
-- Function to the current summary.  This function collects all of the
-- base+offset pairs and then uses @traceFromBases@ to reconstruct
-- them.
arrayAnalysis :: EscapeResult
                 -> Function
                 -> SummaryType
                 -> SummaryType
arrayAnalysis er f summary =
  M.foldlWithKey' (traceFromBases baseResultMap) summary baseResultMap
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
traceFromBases :: Map Value (Value, [Value], EscapeGraph)
                  -> SummaryType
                  -> Value
                  -> (Value, [Value], EscapeGraph)
                  -> SummaryType
traceFromBases baseResultMap summary base (result, _, eg) =
  case argumentsForValue eg base of
    [] -> summary
    args ->
      let depth = traceBackwards baseResultMap result 1
      in foldr (addToSummary depth) summary args


-- | Update the summary for an argument with a depth.
--
-- The function always keeps the *maximum* array depth it discovers
-- (i.e., inserting an array depth of 1 for an argument that is
-- already recorded as having depth 2 will not make any changes to the
-- summary).
addToSummary :: Int -> Argument -> SummaryType -> SummaryType
addToSummary depth arg summ =
  M.insertWith max arg depth summ

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
                                    })} -> case idxs of
    [] -> error ("GEP <isArrayDeref> with no indices")
    [_] -> Just (Value inst, base, idxs, escapeGraphAtLocation er inst)
    (valueContent' -> ConstantC ConstantInt { constantIntValue = 0 }) :
      (valueContent' -> ConstantC ConstantInt {}) : _ -> Nothing
    _ -> Just (Value inst, base, idxs, escapeGraphAtLocation er inst)
  _ -> Nothing

-- Testing

arraySummaryToTestFormat :: ArrayParamSummary -> Map (String, String) Int
arraySummaryToTestFormat (APS summ) = M.mapKeys argToString summ
  where
    argToString a =
      let f = argumentFunction a
      in (show (functionName f), show (argumentName a))
