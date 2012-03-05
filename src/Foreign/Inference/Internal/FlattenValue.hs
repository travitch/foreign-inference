module Foreign.Inference.Internal.FlattenValue ( flattenValue ) where

import Data.List ( foldl' )
import qualified Data.Set as S

import LLVM.Analysis

-- | Turn a value into a list of all of the possible values it could
-- represent.  This effectively means returning all possible values
-- that phi and select instructions could point to.
flattenValue :: Value -> [Value]
flattenValue = S.toList . flatten' S.empty
  where
    flatten' acc v =
      case v `S.member` acc of
        True -> acc
        False ->
          let acc' = S.insert v acc
          in case valueContent' v of
            InstructionC PhiNode { phiIncomingValues = pvs } ->
              let vs = map fst pvs
              in foldl' flatten' acc' vs
            InstructionC SelectInst { selectTrueValue = tv, selectFalseValue = fv } ->
              foldl' flatten' acc' [tv, fv]
            _ -> v `S.insert` acc'
