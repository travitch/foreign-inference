{-# LANGUAGE ViewPatterns, MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
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
--
-- 3) Should we be tracking stores of arguments through globals?
--    Technically they could change out from under us in some
--    potential threaded interleavings, leaving us with incorrect
--    assumptions.  On the other hand, there are interleavings where
--    this gives us the correct answer and, as C doesn't really have
--    anything to say about threads, this is a legitimate
--    interpretation of the program.
--
-- # Observations on infeasible paths #
--
-- Consider code like
--
-- > if(x > 10) *p = 5;
--
-- If x can never be greater than 10, the path is infeasible and we
-- might conclude that p must not be NULL.  Even though this is not on
-- an infeasible path, this is a safe conclusion (assuming no other
-- references) because we do not lose any functionality by mandating
-- that p not be NULL.
--
-- We do lose functionality in the presence of conditions like:
--
-- > if(!p) ...
--
-- Often, this is error handling code.  Not always, though.  Tying in
-- the error handling code analysis will resolve these cases.
module Foreign.Inference.Analysis.Nullable (
  -- * Interface
  NullableSummary,
  identifyNullable,
  -- * Testing
  nullSummaryToTestFormat
  ) where

import Algebra.Lattice
import Control.Monad.RWS.Strict
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

import Foreign.Inference.Diagnostics
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
identifyNullable :: DependencySummary -> Module -> CallGraph -> EscapeResult
                    -> (NullableSummary, Diagnostics)
identifyNullable ds m cg er = (NS res, diags)
  where
    s0 = M.fromList $ zip (moduleDefinedFunctions m) (repeat S.empty)
    analysis = callGraphSCCTraversal cg nullableAnalysis s0
    constData = ND er undefined ds cg
    (res, diags) = evalRWS analysis constData ()

-- | The dataflow fact for this analysis
data NullInfo = NI { mayBeNull :: Set Value  -- ^ The set of variables that may be NULL
                   , accessedUnchecked :: Set Value -- ^ Variables that were accessed before they were known to be not NULL
                   }
                deriving (Eq, Ord, Show)

data NullData = ND { escapeResult :: EscapeResult
                   , moduleSummary :: SummaryType
                   , dependencySummary :: DependencySummary
                   , callGraph :: CallGraph
                   }


instance MeetSemiLattice NullInfo where
  meet = meetNullInfo

instance BoundedMeetSemiLattice NullInfo where
  top = NI S.empty S.empty

type AnalysisMonad = RWS NullData Diagnostics ()

instance DataflowAnalysis AnalysisMonad NullInfo where
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
nullableAnalysis :: Function -> SummaryType -> AnalysisMonad SummaryType
nullableAnalysis f summ = do
  -- Run this sub-analysis step with a modified environment - the
  -- summary component is the current module summary (given to us by
  -- the SCC traversal).
  --
  -- The initial state of the dataflow analysis is top -- all pointer
  -- parameters are NULLable.
  let envMod e = e { moduleSummary = summ }
  localInfo <- local envMod (forwardDataflow top f)

  let exitInfo = HM.lookupDefault err exitInst localInfo
      justArgs = S.fromList $ mapMaybe toArg $ S.toList (accessedUnchecked exitInfo)

  -- Update the module symmary with the set of pointer parameters that
  -- we have proven are accessed unchecked.
  return $! M.insert f justArgs summ
  where
    exitInst = functionExitInstruction f
    err = error "NullAnalysis: exit instruction not in dataflow result"

-- | First, process the incoming CFG edges to learn about pointers
-- that are known to be non-NULL.  Then use this updated information
-- to identify pointers that are dereferenced when they *might* be
-- NULL.  Also map these possibly-NULL pointers to any corresponding
-- parameters.
nullTransfer :: NullInfo -> Instruction -> [CFGEdge] -> AnalysisMonad NullInfo
nullTransfer ni i edges = do
  -- Figure out what the points-to escape graph is at this node, and
  -- then compute ni' (updated info about what pointers are NULL)
  -- based on the set of incoming CFG edges.
  er <- asks escapeResult
  let eg = escapeGraphAtLocation er i
      ni' = removeNonNullPointers ni edges

  case i of
    CallInst { callFunction = calledFunc, callArguments = args } ->
      callTransfer eg ni' calledFunc (map fst args)
    InvokeInst { invokeFunction = calledFunc, invokeArguments = args } ->
      callTransfer eg ni' calledFunc (map fst args)
    -- Stack allocated pointers start off as NULL
    AllocaInst {} -> case isPointerPointer i of
      True -> return $! recordPossiblyNull (Value i) ni'
      False -> return ni'
    LoadInst { loadAddress =
      (valueContent' -> InstructionC GetElementPtrInst { getElementPtrValue =
        (valueContent' -> InstructionC LoadInst { loadAddress = ptr })})} ->
      let ni'' = recordIfMayBeNull eg ni' ptr
      in case isPointer i of
        False -> return ni''
        True -> return $! recordPossiblyNull (Value i) ni''
    LoadInst { loadAddress =
      (valueContent' -> InstructionC GetElementPtrInst { getElementPtrValue = ptr })} ->
      let ni'' = recordIfMayBeNull eg ni' ptr
      in case isPointer i of
        False -> return ni''
        True -> return $! recordPossiblyNull (Value i) ni''
    -- For these two instructions, if the ptr is in the may be null set,
    -- it is a not-null pointer.  Note that the result of the load (if a
    -- pointer) could also be NULL.
    LoadInst { loadAddress =
      (valueContent' -> InstructionC LoadInst { loadAddress = ptr }) } ->
      let ni'' = recordIfMayBeNull eg ni' ptr
      in case isPointer i of
        False -> return ni''
        True -> return $! recordPossiblyNull (Value i) ni''
    AtomicRMWInst { atomicRMWPointer = ptr } ->
      return $! recordIfMayBeNull eg ni' ptr

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
      return $! recordAndClobber eg ni' ptr newVal

    -- Similar, but storing directly to an argument.  This could happen
    -- if the module has been reg2mem-ed.  This case is a little
    -- different because the argument acts as a location (this is the
    -- strange off-by-one behavior of arguments versus allocas/globals).
    StoreInst { storeAddress = (valueContent' -> ArgumentC a)
              , storeValue = newVal
              } ->
      return $! recordAndClobber eg ni' (Value a) newVal

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
      return $! maybeClobber ni' ptr newVal
    AtomicCmpXchgInst { atomicCmpXchgPointer = ptr
                      , atomicCmpXchgNewValue = newVal } ->
      return $! recordAndClobber eg ni' ptr newVal
    _ -> return ni'

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
    process' ni v1 (cond True)
  InstructionC ICmpInst { cmpPredicate = ICmpEq
                        , cmpV2 = (valueContent' -> InstructionC LoadInst { loadAddress = v2 } )
                        , cmpV1 = (valueContent -> ConstantC ConstantPointerNull {}) } ->
    process' ni v2 (cond True)
  InstructionC ICmpInst { cmpPredicate = ICmpNe
                        , cmpV1 = (valueContent' -> InstructionC LoadInst { loadAddress = v1 } )
                        , cmpV2 = (valueContent -> ConstantC ConstantPointerNull {}) } ->
    process' ni v1 (cond False)
  InstructionC ICmpInst { cmpPredicate = ICmpNe
                        , cmpV2 = (valueContent' -> InstructionC LoadInst { loadAddress = v2 } )
                        , cmpV1 = (valueContent -> ConstantC ConstantPointerNull {}) } ->
    process' ni v2 (cond False)
  _ -> ni

process' :: NodeInfo -> Value -> Bool -> NullInfo
process' ni val isNull =
  case isNull of
    True -> ni
    False -> recordNotNull val ni

-- | A split out transfer function for function calls.  Looks up
-- summary values for called functions/params and records relevant
-- information in the current dataflow fact.
callTransfer :: EscapeGraph -> NullInfo -> Value -> [Value] -> AnalysisMonad NullInfo
callTransfer eg ni calledFunc args = do
  cg <- asks callGraph
  let callTargets = callValueTargets cg calledFunc
  foldM callTransferDispatch ni callTargets
  where
    callTransferDispatch info target = case valueContent' target of
      FunctionC f -> do
        summ <- asks moduleSummary
        definedFunctionTransfer eg summ f info args
      ExternalFunctionC e -> do
        summ <- asks dependencySummary
        externalFunctionTransfer eg summ e info args

definedFunctionTransfer :: EscapeGraph -> SummaryType -> Function
                           -> NullInfo -> [Value] -> AnalysisMonad NullInfo
definedFunctionTransfer eg summ f ni args =
  return $! foldl' markArgNotNullable ni indexedNotNullArgs
  where
    err = error ("No Function summary for " ++ show (functionName f))
    formals = functionParameters f
    notNullableArgs = M.findWithDefault err f summ
    isNotNullable (a, _) = S.member a notNullableArgs
    -- | Pairs of not-nullable formals/actuals
    indexedNotNullArgs = filter isNotNullable $ zip formals args
    markArgNotNullable info (_, a) = addUncheckedAccess eg info a

externalFunctionTransfer :: EscapeGraph -> DependencySummary -> ExternalFunction
                            -> NullInfo -> [Value] -> AnalysisMonad NullInfo
externalFunctionTransfer eg summ e ni args =
  foldM markIfNotNullable ni indexedArgs
  where
    errMsg = "No ExternalFunction summary for " ++ show (externalFunctionName e)
    indexedArgs = zip [0..] args
    markIfNotNullable info (ix, arg) =
      case lookupArgumentSummary summ e ix of
        Nothing -> do
          emitWarning Nothing "NullAnalysis" errMsg
          return info
        Just attrs -> case PANotNull `elem` attrs of
          False -> return info
          True -> return $! addUncheckedAccess eg info arg

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