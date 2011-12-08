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

import Foreign.Inference.Internal.ValueArguments

-- | Note, this could be a Set (Argument, Instruction) where the
-- Instruction is the fact we saw that led us to believe that Argument
-- is not nullable.
type NullableSummary = Set Argument

-- | The top-level entry point of the nullability analysis
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

-- | First, process the incoming CFG edges to learn about pointers
-- that are known to be non-NULL.  Then use this updated information
-- to identify pointers that are dereferenced when they *might* be
-- NULL.  Also map these possibly-NULL pointers to any corresponding
-- parameters.
nullTransfer :: NullData -> NullInfo -> Instruction -> [CFGEdge] -> NullInfo
nullTransfer nd ni i edges = case i of
  -- Stack allocated pointers start off as NULL
  AllocaInst {} -> case isPointerPointer i of
    True -> recordPossiblyNull ni' (Value i)
    False -> ni'
  -- For these two instructions, if the ptr is in the may be null set,
  -- it is a not-null pointer.  Note that the result of the load (if a
  -- pointer) could also be NULL.
  LoadInst { loadAddress = ptr } ->
    let ni'' = recordIfMayBeNull eg ni' ptr
    in case isPointer i of
      False -> ni''
      True -> recordPossiblyNull ni'' (Value i)
  AtomicRMWInst { atomicRMWPointer = ptr } ->
    recordIfMayBeNull eg ni' ptr
  -- For these instructions, if the ptr is treated the same.  However,
  -- after these instructions execute, the location stored to could
  -- contain NULL again.  This is conservative - we could more closely inspect
  -- what is being assigned to the pointer, but ...
  StoreInst { storeAddress = ptr, storeValue = newVal } ->
    recordAndClobber eg ni' ptr newVal
  AtomicCmpXchgInst { atomicCmpXchgPointer = ptr
                    , atomicCmpXchgNewValue = newVal } ->
    recordAndClobber eg ni' ptr newVal
  _ -> ni
  where
    ni' = removeNonNullPointers ni edges
    eg = escapeGraphAtLocation (escapeResult nd) i

-- | Check if the *exact* pointer is in the set of may-be-null
-- pointers.  If it is, try to map it back to an argument before
-- inserting it into the non-nullable set.
recordIfMayBeNull :: EscapeGraph -> NullInfo -> Value -> NullInfo
recordIfMayBeNull eg ni ptr =
  case S.member ptr (mayBeNull ni) of
    -- The access is safe
    False -> ni
    -- The access is unsafe and we need to record that this pointer
    -- (and especially any arguments it may point to) are not
    -- NULLABLE. (accessedUnchecked)
    True ->
      let args = map Value $ argumentsForValue eg ptr
          newUnchecked = S.fromList (ptr : args)
      in ni { accessedUnchecked = S.union (accessedUnchecked ni) newUnchecked }

-- | As in @recordIfMayBeNull@, record ptr as non-nullable if
-- necessary.  Additionally, clobber @ptr@ since it could be NULL
-- again after this operation.  Only clobber if @newVal@ might be
-- NULL.  Various pointer values can never be NULL (e.g., variables).
recordAndClobber :: EscapeGraph -> NullInfo -> Value -> Value -> NullInfo
recordAndClobber eg ni ptr newVal =
  recordPossiblyNull ni' ptr
  where
    ni' = recordIfMayBeNull eg ni ptr

-- | Examine the incoming edges and, if any tell us that a variable is
-- *not* NULL, remove that variable from the set of maybe null
-- pointers.
--
-- Note that all incoming edges must be consistent.  If there are two
-- incoming edges and only one says that the pointer is not null, that
-- doesn't help (since it might still be null on the other branch).
-- As a simplifying shortcut, only bother to add information for
-- single edges.
removeNonNullPointers :: NullInfo -> [CFGEdge] -> NullInfo
removeNonNullPointers ni [TrueEdge v] = processCFGEdge ni id v
removeNonNullPointers ni [FalseEdge v] = processCFGEdge ni not v
removeNonNullPointers ni _ = ni

processCFGEdge :: NullInfo -> (Bool -> Bool) -> Value -> NullInfo
processCFGEdge ni cond v = case valueContent v of
  InstructionC ICmpInst { cmpPredicate = ICmpEq, cmpV1 = v1
                        , cmpV2 = (valueContent -> ConstantC ConstantPointerNull {}) } ->
    process' v1 (cond True)
  InstructionC ICmpInst { cmpPredicate = ICmpEq, cmpV2 = v2
                        , cmpV1 = (valueContent -> ConstantC ConstantPointerNull {}) } ->
    process' v2 (cond True)
  InstructionC ICmpInst { cmpPredicate = ICmpNe, cmpV1 = v1
                        , cmpV2 = (valueContent -> ConstantC ConstantPointerNull {}) } ->
    process' v1 (cond False)
  InstructionC ICmpInst { cmpPredicate = ICmpNe, cmpV2 = v2
                        , cmpV1 = (valueContent -> ConstantC ConstantPointerNull {}) } ->
    process' v2 (cond False)
  _ -> ni
  where
    process' val isNull = case isNull of
      True -> ni
      False -> recordPossiblyNull ni val

-- Helpers
toArg :: Value -> Maybe Argument
toArg v = case valueContent v of
  ArgumentC a -> Just a
  _ -> Nothing

isPointer :: IsValue a => a -> Bool
isPointer v = case valueType v of
  TypePointer _ _ -> True
  _ -> False

isPointerPointer :: IsValue a => a -> Bool
isPointerPointer v = case valueType v of
  TypePointer (TypePointer _ _) _ -> True
  _ -> False

-- | Helper to record a possibly null pointer into a dataflow fact
recordPossiblyNull :: NullInfo -> Value -> NullInfo
recordPossiblyNull ni v = ni { mayBeNull = S.insert v (mayBeNull ni) }
