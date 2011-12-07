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
  M.foldlWithKey' (traceFromBases f baseResultMap) summary baseResultMap
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


-- | If the given base value is an Argument, convert it to an Argument
-- and return it.  Otherwise, return Nothing.
extractArgument :: IsValue a => a -> Maybe Argument
extractArgument val = case valueContent' val of
  ArgumentC a -> Just a
  _ -> Nothing

-- | Figure out which arguments, if any, correspond to the given value
-- in the points-to escape graph (flow-sensitive points-to
-- information).
--
-- This function makes a best effort to handle struct references.
argumentsForValue :: EscapeGraph -> Value -> [Argument]
argumentsForValue eg v =
  case valueContent' v of
    InstructionC LoadInst { loadAddress = la } ->
      case argumentsForValue' eg la of
        [] -> argumentsForLoad eg la
        as -> as
    _ -> argumentsForValue' eg v

argumentsForValue' :: EscapeGraph -> Value -> [Argument]
argumentsForValue' eg v =
  case valueInGraph eg v of
    False -> []
    True ->
      let targets = S.toList $ localPointsTo eg v
          targetVals = map escapeNodeValue targets
      in mapMaybe extractArgument targetVals

argumentsForLoad :: EscapeGraph -> Value -> [Argument]
argumentsForLoad eg v =
  case getLoadedValue eg v of
    Nothing -> []
    Just base -> case valueInGraph eg base of
      False -> []
      True ->
        let targets = S.toList $ localPointsTo eg base
            targetVals = map escapeNodeValue targets
        in mapMaybe extractArgument targetVals

getLoadedValue :: EscapeGraph -> Value -> Maybe Value
getLoadedValue eg la = case valueContent' la of
  ConstantC ConstantValue { constantInstruction =
    GetElementPtrInst { getElementPtrValue = base
                      , getElementPtrIndices = idxs
                      } } ->
    getGepBase base idxs
  InstructionC GetElementPtrInst { getElementPtrValue = base
                                 , getElementPtrIndices = idxs
                                 } ->
    getGepBase base idxs
  _ -> Just la
  where
    getGepBase base idxs =
      case valueInGraph eg base of
        False -> Just la
        True -> case idxs of
          [] -> error ("ArrayAnalysis: GEP with no indices: " ++ show la)
          [_] -> followEscapeEdge eg base Array
          (valueContent -> ConstantC ConstantInt { constantIntValue = 0}) :
            (valueContent -> ConstantC ConstantInt { constantIntValue = fieldNo}) : _ ->
              followEscapeEdge eg base (Field (fromIntegral fieldNo) (getBaseType base))
          _ -> followEscapeEdge eg base Array


getBaseType :: Value -> Type
getBaseType base = case valueType base of
  TypePointer t _ -> t
  _ -> error ("Array base value has illegal type: " ++ show base)

-- | Update the summary for an argument with a depth
addToSummary :: Function -> Int -> Argument -> ArrayParamSummary -> ArrayParamSummary
addToSummary f depth arg summ =
  M.insertWith max (show (functionName f), show (argumentName arg)) depth summ

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