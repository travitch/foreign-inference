{-# LANGUAGE ViewPatterns, MultiParamTypeClasses #-}
-- | This module defines a Nullable pointer analysis
--
-- Nullable pointers are those pointers that are checked against NULL
-- before they are used.
module Foreign.Inference.Nullable (
  NullableSummary,
  identifyNullable
  ) where

import Algebra.Lattice
import Data.HashMap.Strict ( HashMap )
import qualified Data.HashMap.Strict as M
import Data.Maybe ( mapMaybe )
import Data.Set ( Set )
import qualified Data.Set as S

import Data.LLVM
import Data.LLVM.CallGraph
import Data.LLVM.CFG
import Data.LLVM.Analysis.CallGraphSCCTraversal
import Data.LLVM.Analysis.Dataflow
import Data.LLVM.Analysis.Escape

type NullableSummary = Set Argument

identifyNullable :: CallGraph -> EscapeResult -> NullableSummary
identifyNullable cg er = callGraphSCCTraversal cg (nullableAnalysis er) S.empty

-- | The dataflow fact for this analysis
data NullInfo = NI { mayBeNull :: Set Value  -- ^ The set of variables that may be NULL
                   , accessedUnchecked :: Set Value -- ^ Variables that were accessed before they were known to be not NULL
                   }
                deriving (Eq, Ord)

data NullData = ND { escapeResult :: EscapeResult }


instance MeetSemiLattice NullInfo where
  meet = meetNullInfo

instance BoundedMeetSemiLattice NullInfo where
  top = NI S.empty S.empty

instance DataflowAnalysis NullInfo NullData where
  transfer = nullTransfer

-- | The meet operator for @NullInfo@
meetNullInfo :: NullInfo -> NullInfo -> NullInfo
meetNullInfo ni1 ni2 =
  NI { mayBeNull = mayBeNull ni1 `S.union` mayBeNull ni2
     , accessedUnchecked = accessedUnchecked ni1 `S.union` accessedUnchecked ni2
     }

-- | The analysis that is applied to every function in the call graph.
-- It runs a dataflow analysis over the function to identify the
-- parameters that are used before they are known to be non-NULL.
--
-- This set of arguments is added to the global summary data (set of
-- all non-nullable arguments).
nullableAnalysis :: EscapeResult -> Function -> NullableSummary -> NullableSummary
nullableAnalysis er f summ = summ `S.union` justArgs
  where
    -- The global data is the escape analysis result
    nd = ND er
    -- Start off by assuming that all pointer parameters are NULL
    s0 = NI { mayBeNull = S.fromList $ map Value $ filter isPointer (functionParameters f)
            , accessedUnchecked = S.empty
            }
    localInfo = forwardDataflow nd s0 f
    exitInst = functionExitInstruction f
    err = error "NullAnalysis: exit instruction not in dataflow result"
    exitInfo = M.lookupDefault err exitInst localInfo
    justArgs = S.fromList $ mapMaybe toArg $ S.toList (accessedUnchecked exitInfo)

nullTransfer :: NullData -> NullInfo -> Instruction -> [CFGEdge] -> NullInfo
nullTransfer nd ni i edges = undefined


-- Helpers
toArg :: Value -> Maybe Argument
toArg v = case valueContent v of
  ArgumentC a -> Just a
  _ -> Nothing

isPointer :: IsValue a => a -> Bool
isPointer v = case valueType v of
  TypePointer _ _ -> True
  _ -> False
