{-# LANGUAGE ViewPatterns, MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
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
import Control.DeepSeq
import Control.Monad.RWS.Strict
import Data.List ( foldl' )
import Data.Map ( Map )
import qualified Data.Map as M
import Data.Maybe ( mapMaybe )
import Data.Set ( Set )
import qualified Data.Set as S
import FileLocation

import Data.LLVM
import Data.LLVM.CallGraph
import Data.LLVM.CFG
import Data.LLVM.Analysis.CallGraphSCCTraversal
import Data.LLVM.Analysis.Dataflow

import Foreign.Inference.Diagnostics
import Foreign.Inference.Interface

-- import Text.Printf
-- import Debug.Trace

-- debug' :: c -> String -> c
-- debug' = flip trace


type SummaryType = Map Function (Set Argument)

-- | Note, this could be a Set (Argument, Instruction) where the
-- Instruction is the fact we saw that led us to believe that Argument
-- is not nullable.
newtype NullableSummary = NS { unNS :: SummaryType }

instance Eq NullableSummary where
  (NS s1) == (NS s2) = s1 == s2

instance SummarizeModule NullableSummary where
  summarizeFunction _ _ = []
  summarizeArgument = summarizeNullArgument

summarizeNullArgument :: Argument -> NullableSummary -> [ParamAnnotation]
summarizeNullArgument a (NS s) = case a `S.member` nonNullableArgs of
  False -> []
  True -> [PANotNull]
  where
    f = argumentFunction a
    errMsg = error ("Function not in summary: " ++ show (functionName f))
    nonNullableArgs = M.findWithDefault errMsg f s


-- | The top-level entry point of the nullability analysis
identifyNullable :: DependencySummary -> Module -> CallGraph
                    -> (NullableSummary, Diagnostics)
identifyNullable ds m cg = (NS res, diags)
  where
    s0 = M.fromList $ zip (moduleDefinedFunctions m) (repeat S.empty)
    analysis = callGraphSCCTraversal cg nullableAnalysis s0
    constData = ND M.empty ds cg
    (res, diags) = evalRWS analysis constData ()

-- | The dataflow fact for this analysis.  The @mayBeNull@ set tracks
-- the arguments and local variables that may be null at a program
-- point.  For locals, the only thing in the set is the alloca
-- representing it.
data NullInfo = NI { mayBeNull :: Set Value  -- ^ The set of variables that may be NULL
                   , accessedUnchecked :: Set Value -- ^ Variables that were accessed before they were known to be not NULL
                   }
                deriving (Eq, Ord, Show)

data NullData = ND { moduleSummary :: SummaryType
                   , dependencySummary :: DependencySummary
                   , callGraph :: CallGraph
                   }

instance NFData NullInfo where
  rnf ni@(NI s1 s2) = s1 `deepseq` s2 `deepseq` ni `seq` ()

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
      fact0 = top { mayBeNull = S.fromList (map Value (functionParameters f)) }
  localInfo <- local envMod (forwardBlockDataflow fact0 f)

  exitInfo <- local envMod (dataflowResult localInfo exitInst)
--  let exitInfo = dataflowResult
--    exitInfo = HM.lookupDefault errMsg exitInst localInfo
  let justArgs = S.fromList $ mapMaybe toArg $ S.toList (accessedUnchecked exitInfo)

  -- Update the module symmary with the set of pointer parameters that
  -- we have proven are accessed unchecked.
  return $! M.insert f justArgs summ
  where
    exitInst = functionExitInstruction f
--    errMsg = $(err "NullAnalysis: exit instruction not in dataflow result")

-- | First, process the incoming CFG edges to learn about pointers
-- that are known to be non-NULL.  Then use this updated information
-- to identify pointers that are dereferenced when they *might* be
-- NULL.  Also map these possibly-NULL pointers to any corresponding
-- parameters.
nullTransfer :: NullInfo -> Instruction -> [CFGEdge] -> AnalysisMonad NullInfo
nullTransfer ni i edges = do
  -- Compute ni' (updated info about what pointers are NULL) based on
  -- the set of incoming CFG edges.
  let ni' = removeNonNullPointers ni edges

  case i of
    CallInst { callFunction = calledFunc, callArguments = args } ->
      callTransfer ni' calledFunc (map fst args)
    InvokeInst { invokeFunction = calledFunc, invokeArguments = args } ->
      callTransfer ni' calledFunc (map fst args)
    -- Stack allocated pointers start off as NULL
    AllocaInst {} -> case isPointerPointer i of
      True -> return $! recordPossiblyNull (Value i) ni'
      False -> return ni'

    -- Attempt at handling loads and stores more simply and uniformly.

    LoadInst { loadAddress = ptr } ->
      let ni'' = recordIfMayBeNull ni' ptr
      in case isPointer i of
        False -> return ni''
        -- The pointer that is returned is always considered to be
        -- possibly null
        True -> return $! recordPossiblyNull (Value i) ni''
    StoreInst { storeAddress = ptr
              , storeValue = newVal } ->
      let ni'' = recordIfMayBeNull ni' ptr
      in case isPointer newVal of
        False -> return ni''
        True -> return $! maybeClobber ni'' ptr newVal

    AtomicRMWInst { atomicRMWPointer = ptr } ->
      return $! recordIfMayBeNull ni' ptr

    AtomicCmpXchgInst { atomicCmpXchgPointer = ptr
                      , atomicCmpXchgNewValue = newVal } ->
      let ni'' = recordIfMayBeNull ni' ptr
      in case isPointer newVal of
        False -> return ni''
        True -> return $! maybeClobber ni'' ptr newVal

    _ -> return ni'

-- | Clobber the value of @ptr@ (mark it as possibly NULL due to
-- assignment).
maybeClobber :: NullInfo -> Value -> Value -> NullInfo
maybeClobber ni ptr _ {-newVal-} = recordPossiblyNull ptr ni

recordIfMayBeNull :: NullInfo -> Value -> NullInfo
recordIfMayBeNull ni ptr =
  case memAccessBase ptr of
    -- We don't reason about all pointer dereferences.  The direct
    -- dereference of an alloca or global variable is *always* safe
    -- (since those pointers are maintained by the compiler/runtime).
    Nothing -> ni
    Just b ->
      case S.member b (mayBeNull ni) of
        False -> ni
        True -> addUncheckedAccess ni b

-- | Given a value that is being dereferenced by an instruction
-- (either a load, store, or atomic memory op), determine the *base*
-- address that is being dereferenced.
--
-- Not all base values need to be analyzed.  For example, globals and
-- allocas are *always* safe to dereference.
--
-- This function strips off intermediate bitcasts.
memAccessBase :: Value -> Maybe Value
memAccessBase ptr =
  case valueContent' ptr of
    GlobalVariableC _ -> Nothing
    InstructionC AllocaInst {} -> Nothing
    -- For optimized code, arguments (which we care about) can be
    -- loaded/stored to directly (without an intervening alloca).
    ArgumentC a -> Just (Value a)
    -- In this case, we have two levels of dereference.  The first
    -- level (la) is a global or alloca (or result of another
    -- load/GEP).  This represents a source-level dereference of a
    -- local pointer.
    InstructionC LoadInst { loadAddress = la } -> Just $ stripBitcasts la
    -- This case captures array/field accesses: a[x] The base
    -- loadAddress here represents the load of a from a local or
    -- global.
    InstructionC GetElementPtrInst { getElementPtrValue =
      (valueContent' -> InstructionC LoadInst { loadAddress = la}) } ->
      Just $ stripBitcasts la
    -- This case might not really be necessary...
    InstructionC GetElementPtrInst { getElementPtrValue = v } ->
      Just $ stripBitcasts v
    _ -> Just $ stripBitcasts ptr

-- | Record the given @ptr@ as being accessed unchecked.
-- Additionally, determine which function arguments @ptr@ may alias at
-- this program point (based on the points-to escape graph) and also
-- record that as being accessed unchecked.
--
-- FIXME: Look into adding a separate annotation here for arguments
-- that *may* be accessed unchecked versus arguments that *must* be
-- accessed unchecked.  Just check the size of the set returned by
-- argumentsForValue to determine which case we are in.
addUncheckedAccess :: NullInfo -> Value -> NullInfo
addUncheckedAccess ni ptr =
  let ni' = ni { accessedUnchecked = S.union (accessedUnchecked ni) newUnchecked }
  in ni'
  where
    -- | FIXME: Here is the spot we need to pick out arguments
    args = case valueContent' ptr of
      ArgumentC a -> [Value a]
      _ -> []
--      [] -- map Value $ argumentsForValue eg ptr
    newUnchecked = S.fromList (ptr : args)

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

-- | Given a condition from a CFG edge, determine if the condition
-- gives us information about the NULL-ness of a pointer.  If so,
-- update the NullInfo.
processCFGEdge :: NullInfo -> (Bool -> Bool) -> Value -> NullInfo
processCFGEdge ni cond v = case valueContent v of
  InstructionC ICmpInst { cmpPredicate = ICmpEq
                        , cmpV1 = (valueContent' -> InstructionC LoadInst { loadAddress = v1 } )
                        , cmpV2 = (valueContent -> ConstantC ConstantPointerNull {}) } ->
    process' ni v1 (cond True)
  InstructionC ICmpInst { cmpPredicate = ICmpEq
                        , cmpV1 = (valueContent' -> ArgumentC v1)
                        , cmpV2 = (valueContent -> ConstantC ConstantPointerNull {}) } ->
    process' ni (Value v1) (cond True)

  InstructionC ICmpInst { cmpPredicate = ICmpEq
                        , cmpV2 = (valueContent' -> InstructionC LoadInst { loadAddress = v2 } )
                        , cmpV1 = (valueContent -> ConstantC ConstantPointerNull {}) } ->
    process' ni v2 (cond True)
  InstructionC ICmpInst { cmpPredicate = ICmpEq
                        , cmpV2 = (valueContent' -> ArgumentC v2)
                        , cmpV1 = (valueContent -> ConstantC ConstantPointerNull {}) } ->
    process' ni (Value v2) (cond True)

  InstructionC ICmpInst { cmpPredicate = ICmpNe
                        , cmpV1 = (valueContent' -> InstructionC LoadInst { loadAddress = v1 } )
                        , cmpV2 = (valueContent -> ConstantC ConstantPointerNull {}) } ->
    process' ni v1 (cond False)
  InstructionC ICmpInst { cmpPredicate = ICmpNe
                        , cmpV1 = (valueContent' -> ArgumentC v1)
                        , cmpV2 = (valueContent -> ConstantC ConstantPointerNull {}) } ->
    process' ni (Value v1) (cond False)

  InstructionC ICmpInst { cmpPredicate = ICmpNe
                        , cmpV2 = (valueContent' -> InstructionC LoadInst { loadAddress = v2 } )
                        , cmpV1 = (valueContent -> ConstantC ConstantPointerNull {}) } ->
    process' ni v2 (cond False)
  InstructionC ICmpInst { cmpPredicate = ICmpNe
                        , cmpV2 = (valueContent' -> ArgumentC v2)
                        , cmpV1 = (valueContent -> ConstantC ConstantPointerNull {}) } ->
    process' ni (Value v2) (cond False)

  -- FIXME: If we use gvn, we need to be able to handle conditions
  -- that are Phi nodes here.  One approach would be to accumulate all
  -- of the (Value, IsNull) pairs here and, if they are all the same,
  -- conclude that the value is indeed null...
  --
  -- GVN is useful to look through some memory references to improve
  -- precision, so this would be worth trying.  On the other hand, it
  -- could potentially make this analysis a little imprecise if GVN is
  -- too aggressive and combines unrelated branches.

  _ -> ni

process' :: NullInfo -> Value -> Bool -> NullInfo
process' ni val isNull =
  case isNull of
    True -> ni
    False -> recordNotNull val ni

-- | A split out transfer function for function calls.  Looks up
-- summary values for called functions/params and records relevant
-- information in the current dataflow fact.
callTransfer :: NullInfo -> Value -> [Value] -> AnalysisMonad NullInfo
callTransfer ni calledFunc args = do
  cg <- asks callGraph
  let callTargets = callValueTargets cg calledFunc
  ni' <- foldM callTransferDispatch ni callTargets
  -- We also learn information about pointers that are not null if
  -- this is a call through a function pointer (calling a NULL
  -- function pointer is illegal)
  case isIndirectCallee calledFunc of
    False -> return ni'
    True -> return (recordIfMayBeNull ni' calledFunc)
  where
    callTransferDispatch info target = case valueContent' target of
      FunctionC f -> do
        summ <- asks moduleSummary
        definedFunctionTransfer summ f info args
      ExternalFunctionC e -> do
        summ <- asks dependencySummary
        externalFunctionTransfer summ e info args
      _ -> $(err "Unexpected value; indirect calls should be resolved")

isIndirectCallee :: Value -> Bool
isIndirectCallee val =
  case valueContent' val of
    FunctionC _ -> False
    ExternalFunctionC _ -> False
    _ -> True

definedFunctionTransfer :: SummaryType -> Function
                           -> NullInfo -> [Value] -> AnalysisMonad NullInfo
definedFunctionTransfer summ f ni args =
  return $! foldl' markArgNotNullable ni indexedNotNullArgs
  where
    errMsg = error ("No Function summary for " ++ show (functionName f))
    formals = functionParameters f
    notNullableArgs = M.findWithDefault errMsg f summ
    isNotNullable (a, _) = S.member a notNullableArgs
    -- | Pairs of not-nullable formals/actuals
    indexedNotNullArgs = filter isNotNullable $ zip formals args
    markArgNotNullable info (_, a) = recordIfMayBeNull info a

externalFunctionTransfer :: DependencySummary -> ExternalFunction
                            -> NullInfo -> [Value] -> AnalysisMonad NullInfo
externalFunctionTransfer summ e ni args =
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
          True -> return $! recordIfMayBeNull info arg

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