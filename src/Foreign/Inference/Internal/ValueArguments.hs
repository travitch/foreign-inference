{-# LANGUAGE ViewPatterns #-}
module Foreign.Inference.Internal.ValueArguments (
  argumentsForValue
  ) where

import Data.Maybe ( mapMaybe )
import qualified Data.Set as S

import Data.LLVM
import Data.LLVM.Analysis.Escape

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

-- | If the given base value is an Argument, convert it to an Argument
-- and return it.  Otherwise, return Nothing.
extractArgument :: IsValue a => a -> Maybe Argument
extractArgument val = case valueContent' val of
  ArgumentC a -> Just a
  _ -> Nothing
