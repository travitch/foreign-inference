{-# LANGUAGE ViewPatterns, MultiParamTypeClasses #-}
-- | This module defines a Nullable pointer analysis
--
-- Nullable pointers are those pointers that are checked against NULL
-- before they are used.
--
-- Questions:
--
-- 1) How strict should this be? Must a non-nullable pointer be
--    referenced unchecked on *every* path, or does one suffice?
--
-- 2) How conservative should we be with regard to aliasing? Should a
--    may-alias unchecked dereference make the parameter non-nullable?
--    In theory letting may-alias relationships influence us could lead
--    to false positives that make some functions uncallable.  Is this a
--    problem in practice?
module Foreign.Inference.Analysis.Nullable (
  -- * Interface
  NullableSummary,
  identifyNullable,
  -- * Testing
  nullSummaryToTestFormat
  ) where

import Algebra.Lattice
import Data.List ( foldl' )
import Data.Map ( Map )
import qualified Data.Map as M
import qualified Data.HashMap.Strict as HM
import Data.Maybe ( mapMaybe )
import Data.Set ( Set )
import qualified Data.Set as S

import Data.LLVM
import Data.LLVM.CallGraph
import Data.LLVM.CFG
import Data.LLVM.Analysis.CallGraphSCCTraversal
import Data.LLVM.Analysis.Dataflow
import Data.LLVM.Analysis.Escape

import Foreign.Inference.Interface
import Foreign.Inference.Internal.ValueArguments

-- import Text.Printf
-- import Debug.Trace

-- debug :: c -> String -> c
-- debug = flip trace

type SummaryType = Map Function (Set Argument)

-- | Note, this could be a Set (Argument, Instruction) where the
-- Instruction is the fact we saw that led us to believe that Argument
-- is not nullable.
newtype NullableSummary = NS SummaryType
                        deriving (Eq)

instance SummarizeModule NullableSummary where
  summarizeFunction _ _ = []
  summarizeArgument = summarizeNullArgument

summarizeNullArgument :: Argument -> NullableSummary -> [ParamAnnotation]
summarizeNullArgument a (NS s) = case a `S.member` nonNullableArgs of
  False -> []
  True -> [PANotNull]
  where
    f = argumentFunction a
    err = error ("Function not in summary: " ++ show (functionName f))
    nonNullableArgs = M.findWithDefault err f s


-- | The top-level entry point of the nullability analysis
identifyNullable :: DependencySummary -> Module -> CallGraph -> EscapeResult -> NullableSummary
identifyNullable ds m cg er = NS $ callGraphSCCTraversal cg (nullableAnalysis ds er) s0
  where
    s0 = M.fromList $ zip (moduleDefinedFunctions m) (repeat S.empty)

-- | The dataflow fact for this analysis
data NullInfo = NI { mayBeNull :: Set Value  -- ^ The set of variables that may be NULL
                   , accessedUnchecked :: Set Value -- ^ Variables that were accessed before they were known to be not NULL
                   }
                deriving (Eq, Ord, Show)

data NullData = ND { escapeResult :: EscapeResult
                   , moduleSummary :: SummaryType
                   , dependencySummary :: DependencySummary
                   }


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
nullableAnalysis :: DependencySummary -> EscapeResult -> Function -> SummaryType -> SummaryType
nullableAnalysis ds er f summ = M.insert f justArgs summ
  where
    -- The global data is the escape analysis result
    nd = ND er summ ds
    -- Start off by assuming that all pointer parameters are NULL
    s0 = top
    localInfo = forwardDataflow nd s0 f
    exitInst = functionExitInstruction f
    err = error "NullAnalysis: exit instruction not in dataflow result"
    exitInfo = HM.lookupDefault err exitInst localInfo
    justArgs = S.fromList $ mapMaybe toArg $ S.toList (accessedUnchecked exitInfo)

-- | First, process the incoming CFG edges to learn about pointers
-- that are known to be non-NULL.  Then use this updated information
-- to identify pointers that are dereferenced when they *might* be
-- NULL.  Also map these possibly-NULL pointers to any corresponding
-- parameters.
nullTransfer :: NullData -> NullInfo -> Instruction -> [CFGEdge] -> NullInfo
nullTransfer nd ni i edges = case i {- `debug` printf "%s --> %s\n" (show i) (show ni') -} of
  CallInst { callFunction = calledFunc, callArguments = args } ->
    callTransfer nd eg ni' calledFunc (map fst args)
  InvokeInst { invokeFunction = calledFunc, invokeArguments = args } ->
    callTransfer nd eg ni' calledFunc (map fst args)
  -- Stack allocated pointers start off as NULL
  AllocaInst {} -> case isPointerPointer i of
    True -> recordPossiblyNull (Value i) ni'
    False -> ni'
  LoadInst { loadAddress =
    (valueContent' -> InstructionC GetElementPtrInst { getElementPtrValue =
      (valueContent' -> InstructionC LoadInst { loadAddress = ptr })})} ->
    let ni'' = recordIfMayBeNull eg ni' ptr
    in case isPointer i of
      False -> ni''
      True -> recordPossiblyNull (Value i) ni''
  LoadInst { loadAddress =
    (valueContent' -> InstructionC GetElementPtrInst { getElementPtrValue = ptr })} ->
    let ni'' = recordIfMayBeNull eg ni' ptr
    in case isPointer i of
      False -> ni''
      True -> recordPossiblyNull (Value i) ni''
  -- For these two instructions, if the ptr is in the may be null set,
  -- it is a not-null pointer.  Note that the result of the load (if a
  -- pointer) could also be NULL.
  LoadInst { loadAddress =
    (valueContent' -> InstructionC LoadInst { loadAddress = ptr }) } ->
    let ni'' = recordIfMayBeNull eg ni' ptr
    in case isPointer i of
      False -> ni''
      True -> recordPossiblyNull (Value i) ni''
  AtomicRMWInst { atomicRMWPointer = ptr } ->
    recordIfMayBeNull eg ni' ptr

  -- For these instructions, if the ptr is treated the same.  However,
  -- after these instructions execute, the location stored to could
  -- contain NULL again.  This is conservative - we could more closely inspect
  -- what is being assigned to the pointer, but ...

  -- This case handles stores through pointers. Example:
  --
  -- > int * x;
  -- > *x = 5; // This line
  --
  -- makes store 5 x.  If x is not known to be non-NULL here, we have
  -- to record x as being non-nullable (accessed without being
  -- checked).  If x is at least a pointer to pointer, then the
  -- pointer value *may* be null after this.  &x cannot be null, of
  -- course.
  StoreInst { storeAddress = (valueContent' -> InstructionC LoadInst { loadAddress = ptr })
            , storeValue = newVal } ->
    recordAndClobber eg ni' ptr newVal

  -- Similar, but storing directly to an argument.  This could happen
  -- if the module has been reg2mem-ed.  This case is a little
  -- different because the argument acts as a location (this is the
  -- strange off-by-one behavior of arguments versus allocas/globals).
  StoreInst { storeAddress = (valueContent' -> ArgumentC a)
            , storeValue = newVal
            } ->
    recordAndClobber eg ni' (Value a) newVal

  -- This is a simpler case - we are storing to some location.
  -- Locations (allocas, globals) are never NULL.  At worst, the
  -- pointer stored at the location is being clobbered.
  --
  -- > int * x;
  -- > x = malloc();
  --
  -- makes: store (malloc) x.  Clearly &x is never NULL, but x may be
  -- NULL after the assignment.
  StoreInst { storeAddress = ptr
            , storeValue = newVal } ->
    maybeClobber ni' ptr newVal
  AtomicCmpXchgInst { atomicCmpXchgPointer = ptr
                    , atomicCmpXchgNewValue = newVal } ->
    recordAndClobber eg ni' ptr newVal
  _ -> ni'
  where
    ni' = removeNonNullPointers ni edges
    eg = escapeGraphAtLocation (escapeResult nd) i

-- | Clobber the value of @ptr@ (mark it as possibly NULL due to
-- assignment).
maybeClobber :: NullInfo -> Value -> Value -> NullInfo
maybeClobber ni ptr newVal = recordPossiblyNull ptr ni

-- | Check if the *exact* pointer is in the set of may-be-null
-- pointers.  If it is, try to map it back to an argument before
-- inserting it into the non-nullable set.
recordIfMayBeNull :: EscapeGraph -> NullInfo -> Value -> NullInfo
recordIfMayBeNull eg ni ptr =
  case S.member ptr (mayBeNull ni) of -- FIXME: Or if it is a field
                                      -- access?  Fields might always
                                      -- be null

    -- The access is safe
    False -> ni
    -- The access is unsafe and we need to record that this pointer
    -- (and especially any arguments it may point to) are not
    -- NULLABLE. (accessedUnchecked)
    True -> addUncheckedAccess eg ni ptr
      -- let args = map Value $ argumentsForValue eg ptr
      --     newUnchecked = S.fromList (ptr : args)
      -- in ni { accessedUnchecked = S.union (accessedUnchecked ni) newUnchecked }

addUncheckedAccess :: EscapeGraph -> NullInfo -> Value -> NullInfo
addUncheckedAccess eg ni ptr =
  ni { accessedUnchecked = S.union (accessedUnchecked ni) newUnchecked }
  where
    args = map Value $ argumentsForValue eg ptr
    newUnchecked = S.fromList (ptr : args)

-- | As in @recordIfMayBeNull@, record ptr as non-nullable if
-- necessary.  Additionally, clobber @ptr@ since it could be NULL
-- again after this operation.  Only clobber if @newVal@ might be
-- NULL.  Various pointer values can never be NULL (e.g., variables).
recordAndClobber :: EscapeGraph -> NullInfo -> Value -> Value -> NullInfo
recordAndClobber eg ni ptr newVal =
  recordPossiblyNull ptr ni'
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
  InstructionC ICmpInst { cmpPredicate = ICmpEq
                        , cmpV1 = (valueContent' -> InstructionC LoadInst { loadAddress = v1 } )
                        , cmpV2 = (valueContent -> ConstantC ConstantPointerNull {}) } ->
    process' v1 (cond True)
  InstructionC ICmpInst { cmpPredicate = ICmpEq
                        , cmpV2 = (valueContent' -> InstructionC LoadInst { loadAddress = v2 } )
                        , cmpV1 = (valueContent -> ConstantC ConstantPointerNull {}) } ->
    process' v2 (cond True)
  InstructionC ICmpInst { cmpPredicate = ICmpNe
                        , cmpV1 = (valueContent' -> InstructionC LoadInst { loadAddress = v1 } )
                        , cmpV2 = (valueContent -> ConstantC ConstantPointerNull {}) } ->
    process' v1 (cond False)
  InstructionC ICmpInst { cmpPredicate = ICmpNe
                        , cmpV2 = (valueContent' -> InstructionC LoadInst { loadAddress = v2 } )
                        , cmpV1 = (valueContent -> ConstantC ConstantPointerNull {}) } ->
    process' v2 (cond False)
  _ -> ni
  where
    process' val isNull = case isNull of
      True -> ni
      False -> recordNotNull val ni

-- | A split out transfer function for function calls.  Looks up
-- summary values for called functions/params and records relevant
-- information in the current dataflow fact.
--
-- Note, does not handle indirect calls yet.
callTransfer :: NullData -> EscapeGraph -> NullInfo -> Value -> [Value] -> NullInfo
callTransfer nd eg ni calledFunc args =
  case valueContent' calledFunc of
    FunctionC f -> definedFunctionTransfer eg (moduleSummary nd) f ni args
    ExternalFunctionC e -> externalFunctionTransfer eg (dependencySummary nd) e ni args

definedFunctionTransfer :: EscapeGraph -> SummaryType -> Function
                           -> NullInfo -> [Value] -> NullInfo
definedFunctionTransfer eg summ f ni args =
  foldl' markArgNotNullable ni indexedNotNullArgs
  where
    err = error ("No Function summary for " ++ show (functionName f))
    formals = functionParameters f
    notNullableArgs = M.findWithDefault err f summ
    isNotNullable (a, _) = S.member a notNullableArgs
    -- | Pairs of not-nullable formals/actuals
    indexedNotNullArgs = filter isNotNullable $ zip formals args
    markArgNotNullable info (_, a) = addUncheckedAccess eg info a

externalFunctionTransfer :: EscapeGraph -> DependencySummary -> ExternalFunction
                            -> NullInfo -> [Value] -> NullInfo
externalFunctionTransfer eg summ e ni args =
  foldl' markIfNotNullable ni indexedArgs
  where
    err = error ("No ExternalFunction summary for " ++ show (externalFunctionName e))
    indexedArgs = zip [0..] args
    markIfNotNullable info (ix, arg) =
      case lookupArgumentSummary summ e ix of
        Nothing -> info
        Just attrs -> case PANotNull `elem` attrs of
          False -> info
          True -> addUncheckedAccess eg info arg

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
recordPossiblyNull :: Value -> NullInfo -> NullInfo
recordPossiblyNull v ni = ni { mayBeNull = S.insert v (mayBeNull ni) }

recordNotNull :: Value -> NullInfo -> NullInfo
recordNotNull v ni = ni { mayBeNull = S.delete v (mayBeNull ni) }

-- Testing

-- | Convert the 'NullableSummary' to a format that is easy to read
-- from a file for testing purposes.
nullSummaryToTestFormat :: NullableSummary -> Map String (Set String)
nullSummaryToTestFormat (NS m) = convert m
  where
    convert = M.mapKeys keyMapper . M.map valMapper . M.filter notEmptySet
    notEmptySet = not . S.null
    valMapper = S.map (show . argumentName)
    keyMapper = show . functionName