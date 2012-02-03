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
--    Just one is fine
--
-- 2) How conservative should we be with regard to aliasing? Should a
--    may-alias unchecked dereference make the parameter non-nullable?
--    In theory letting may-alias relationships influence us could lead
--    to false positives that make some functions uncallable.  Is this a
--    problem in practice?
--
--    May alias is not sufficient - but SSA gives us a lot of
--    flow-sensitive precision.
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
--
--
-- # Complex Dependence Analysis #
--
-- Consider the following code:
--
-- > extern int h(int * p);
-- >
-- > void e(int *p) {
-- >   if(p) *p = 0;
-- > }
-- >
-- > void f(int * p) {
-- >   int cond = 0;
-- >   if(h(p))
-- >     cond = 1;
-- >
-- >   if(!cond)
-- >     *p = 0;
-- > }
-- >
-- > void g(int * p) {
-- >   int cond = 0;
-- >   if(p)
-- >     cond = 1;
-- >
-- >   if(cond)
-- >     *p = 0;
-- > }
--
-- Without interprocedural analysis and expensive theorem prover
-- calls, we cannot track these side conditions (in the example @f@
-- and @g@, based on the @cond@ flag).  At the end of the day, we
-- cannot reason about pointer @p@ in *any* branch whose condition is
-- control- or data-dependent on @p@ (unless the condition is exactly
-- p==NULL or p!=NULL).  Call this property indirect dependence.
--
-- To implement this, augment the condition inspection code.  If the
-- condition is indirectly dependent on @p@, then generate a token
-- with the same ID as the cmp instruction driving the branch.  The
-- false branch gets a negative token and the true branch gets a
-- positive token.  Each token also gets a reference to @p@.  If a
-- token for @p@ is active on a branch, do not reason about @p@.
-- Tokens cancel each other out on control flow joins iff there is at
-- least one negative and at least one positive token and their ID and
-- variable match.
--
-- Alternate formulation: do not reason about @p@ when a read/write to
-- @p@ is control dependent on @p@ while not guarded by a @p!=NULL@ or
-- @p==NULL@ check.
module Foreign.Inference.Analysis.Nullable (
  -- * Interface
  NullableSummary,
  identifyNullable,
  -- * Testing
  nullSummaryToTestFormat
  ) where

import Algebra.Lattice
import Control.Arrow
import Control.Monad.RWS.Strict
import Data.Map ( Map )
import qualified Data.Map as M
import Data.Set ( Set )
import qualified Data.Set as S
import Data.HashMap.Strict ( HashMap )
import qualified Data.HashMap.Strict as HM
import FileLocation

import Data.LLVM
import Data.LLVM.Analysis.CallGraph
import Data.LLVM.Analysis.CDG
import Data.LLVM.Analysis.CFG
import Data.LLVM.Analysis.CallGraphSCCTraversal
import Data.LLVM.Analysis.Dataflow
import Data.LLVM.Analysis.Dominance

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
    errMsg = $err' ("Function not in summary: " ++ show (functionName f))
    nonNullableArgs = M.findWithDefault errMsg f s


-- | The top-level entry point of the nullability analysis
identifyNullable :: DependencySummary -> Module -> CallGraph
                    -> (NullableSummary, Diagnostics)
identifyNullable ds m cg = (NS res, diags)
  where
    s0 = M.fromList $ zip (moduleDefinedFunctions m) (repeat S.empty)
    analysis = callGraphSCCTraversal cg nullableAnalysis s0
    constData = ND M.empty ds cg undefined undefined
    cache = NState HM.empty
    (res, diags) = evalRWS analysis constData cache

data NullData = ND { moduleSummary :: SummaryType
                   , dependencySummary :: DependencySummary
                   , callGraph :: CallGraph
                   , controlDepGraph :: CDG
                   , domTree :: DominatorTree
                   }

data NullState = NState { phiCache :: HashMap Instruction (Maybe Value) }

data NullInfo = NInfo { nullArguments :: Set Argument
                      }
              deriving (Eq, Ord, Show)

instance MeetSemiLattice NullInfo where
  meet = meetNullInfo

instance BoundedMeetSemiLattice NullInfo where
  top = NInfo S.empty

type AnalysisMonad = RWS NullData Diagnostics NullState

instance DataflowAnalysis AnalysisMonad NullInfo where
  transfer = nullTransfer

meetNullInfo :: NullInfo -> NullInfo -> NullInfo
meetNullInfo ni1 ni2 =
  NInfo { nullArguments = nullArguments ni1 `S.union` nullArguments ni2 }

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
  let cfg = mkCFG f
  let envMod e = e { moduleSummary = summ
                   , controlDepGraph = controlDependenceGraph cfg
                   , domTree = dominatorTree cfg
                   }
      args = functionParameters f
      fact0 = top { nullArguments = S.fromList args }
  localInfo <- local envMod (forwardBlockDataflow fact0 f)

  -- FIXME: Filter out unreachable exit nodes (use the CFG)
  let getInstInfo i = local envMod (dataflowResult localInfo i)
  exitInfo <- mapM getInstInfo (functionExitInstructions f)
  let exitInfo' = meets exitInfo
      notNullableArgs = S.fromList args `S.difference` nullArguments exitInfo'

  -- Update the module symmary with the set of pointer parameters that
  -- we have proven are accessed unchecked.
  return $! M.insert f notNullableArgs summ

-- | First, process the incoming CFG edges to learn about pointers
-- that are known to be non-NULL.  Then use this updated information
-- to identify pointers that are dereferenced when they *might* be
-- NULL.  Also map these possibly-NULL pointers to any corresponding
-- parameters.
nullTransfer :: NullInfo
                -> Instruction
                -> [CFGEdge]
                -> AnalysisMonad NullInfo
nullTransfer ni i _ =
  case i of
    LoadInst { loadAddress = ptr } ->
      valueDereferenced ptr ni
    StoreInst { storeAddress = ptr } ->
      valueDereferenced ptr ni
    AtomicRMWInst { atomicRMWPointer = ptr } ->
      valueDereferenced ptr ni
    AtomicCmpXchgInst { atomicCmpXchgPointer = ptr } ->
      valueDereferenced ptr ni

    CallInst { callFunction = calledFunc, callArguments = args } ->
      callTransfer (stripBitcasts calledFunc) (map fst args) ni
    InvokeInst { invokeFunction = calledFunc, invokeArguments = args } ->
      callTransfer (stripBitcasts calledFunc) (map fst args) ni

    _ -> return ni

valueDereferenced :: Value -> NullInfo -> AnalysisMonad NullInfo
valueDereferenced ptr ni =
  case memAccessBase ptr of
    Nothing -> return ni
    Just v -> do
      v' <- mustExecuteValue v
      case v' of
        Nothing -> return ni
        Just mustVal ->
          case valueContent' mustVal of
            ArgumentC a -> return ni { nullArguments = S.delete a (nullArguments ni) }
            _ -> return ni

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
    InstructionC LoadInst { loadAddress = la } ->
      Just (stripBitcasts la)
    -- GEP instructions can appear in sequence for nested field
    -- accesses.  We want the base of the access chain, so walk back
    -- as far as possible and return the lowest-level GEP base.
    InstructionC GetElementPtrInst { getElementPtrValue = base } ->
      memAccessBase base
    _ -> Just (stripBitcasts ptr)

-- | A split out transfer function for function calls.  Looks up
-- summary values for called functions/params and records relevant
-- information in the current dataflow fact.
callTransfer ::  Value
                -> [Value]
                -> NullInfo
                -> AnalysisMonad NullInfo
callTransfer calledFunc args ni = do
  cg <- asks callGraph
  let callTargets = callValueTargets cg calledFunc
  ni' <- foldM callTransferDispatch ni callTargets
  -- We also learn information about pointers that are not null if
  -- this is a call through a function pointer (calling a NULL
  -- function pointer is illegal)
  case isIndirectCallee calledFunc of
    False -> return ni'
    True -> valueDereferenced calledFunc ni'
  where
    callTransferDispatch info target =
      case valueContent' target of
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
  foldM markArgNotNullable ni indexedNotNullArgs
  where
    errMsg = $err' ("No Function summary for " ++ show (functionName f))
    formals = functionParameters f
    notNullableArgs = M.findWithDefault errMsg f summ
    isNotNullable (a, _) = S.member a notNullableArgs
    -- | Pairs of not-nullable formals/actuals
    indexedNotNullArgs = filter isNotNullable $ zip formals args
    markArgNotNullable info (_, a) =
      valueDereferenced a info

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
          True -> valueDereferenced arg info

-- We can tell that a piece of code MUST execute if:
--
-- 1) It has no control dependencies, or
--
-- 2) It has exactly one control dependency (a direct one, and no
-- indirect cdeps) AND all incoming non-backedges are unconditional
-- branches.

-- | Given a Value, figure out which of its sub-values *MUST* be
-- executed on *SOME* call to the function.  For most Values, this is
-- the identity.
--
-- For Select instructions, the result is Nothing (unless we decide to
-- reason more thoroughly about the select condition).
--
-- For Phi nodes, there may be a result for do-while style loops where
-- the first iteration must always be taken.  In this case, return the
-- value that *MUST* be accessed on that iteration.
mustExecuteValue :: Value -> AnalysisMonad (Maybe Value)
mustExecuteValue v =
  case valueContent' v of
    InstructionC SelectInst {} -> return Nothing
    InstructionC i@PhiNode { phiIncomingValues = ivs } -> do
      s <- get
      case HM.lookup i (phiCache s) of
        Just mv -> return mv
        Nothing -> do
          mv <- mustExec' i ivs
          put s { phiCache = HM.insert i mv (phiCache s) }
          return mv
    _ -> return (Just v)

mustExec' :: Instruction -> [(Value, Value)] -> AnalysisMonad (Maybe Value)
mustExec' i ivs = do
  cdg <- asks controlDepGraph
  dt <- asks domTree
  let cdeps = directControlDependencies cdg i
  case cdeps of
    [] -> return Nothing
    [_] -> do
      let predTerms = map (id *** (basicBlockTerminatorInstruction . toBB)) ivs
          nonBackedges = filter (isNotBackedge dt i) predTerms
      case filter (isUnconditional . snd) nonBackedges of
        [] -> return Nothing
        [(v,_)] -> return (Just v)
        _ -> return Nothing
      -- return $! all isUnconditional nonBackedges
    _ -> return Nothing
  where
    toBB v =
      case valueContent v of
        BasicBlockC bb -> bb
        _ -> $err' ("Expected basic block: " ++ show v)
    isUnconditional UnconditionalBranchInst {} = True
    isUnconditional _ = False
    isNotBackedge g inst (_, br) = not (dominates g inst br)


  {-
  shouldAnalyze <- mustExecute i
  case shouldAnalyze of
    False -> return ni
    True ->
      let ni' = removeNonNullPointers ni edges
      in nullTransfer' ni' i edges

nullTransfer' :: NullInfo
                 -> Instruction
                 -> [CFGEdge]
                 -> AnalysisMonad NullInfo
nullTransfer' ni' i _ =
  case i of
    CallInst { callFunction = calledFunc, callArguments = args } -> do
      ni'' <- callTransfer ni' (stripBitcasts calledFunc) (map fst args)
      return $! recordPossiblyNull (Value i) ni''
    InvokeInst { invokeFunction = calledFunc, invokeArguments = args } -> do
      ni'' <- callTransfer ni' (stripBitcasts calledFunc) (map fst args)
      return $! recordPossiblyNull (Value i) ni''

    -- Stack allocated pointers start off as NULL
    AllocaInst {} -> case isPointerPointer i of
      True -> return $! recordPossiblyNull (Value i) ni'
      False -> return ni'

    SelectInst {} -> return $! recordPossiblyNull (Value i) ni'

    VaArgInst {} -> return $! recordPossiblyNull (Value i) ni'

    -- GEP instructions produce a pointer value from another pointer.
    -- If the original base pointer was NULL, then the result is NULL.
    GetElementPtrInst { getElementPtrValue = v } ->
      case stripBitcasts v `S.member` mayBeNull ni' of
        False -> return ni'
        True -> return $! recordPossiblyNull (Value i) ni'

    -- Attempt at handling loads and stores more simply and uniformly.

    LoadInst { loadAddress = ptr } -> do
      ni'' <- recordIfMayBeNull ni' ptr
      case isPointer i of
        False -> return ni''
        -- The pointer that is returned is always considered to be
        -- possibly null
        True -> return $! recordPossiblyNull (Value i) ni''
    StoreInst { storeAddress = ptr } -> recordIfMayBeNull ni' ptr

    AtomicRMWInst { atomicRMWPointer = ptr } -> do
      ni'' <- recordIfMayBeNull ni' ptr
      return $! recordPossiblyNull (Value i) ni''

    AtomicCmpXchgInst { atomicCmpXchgPointer = ptr
                      , atomicCmpXchgNewValue = newVal } -> do
      ni'' <- recordIfMayBeNull ni' ptr
      case isPointer newVal of
        False -> return ni''
        True -> return $! maybeClobber ni'' ptr newVal

    _ -> return ni'

-- We can tell that a piece of code MUST execute if:
--
-- 1) It has no control dependencies, or
--
-- 2) It has exactly one control dependency (a direct one, and no
-- indirect cdeps) AND all incoming non-backedges are unconditional
-- branches.
mustExecute :: Instruction -> AnalysisMonad Bool
mustExecute i = do
  s <- get
  case HM.lookup i (execCache s) of
    Just b -> return b
    Nothing -> do
      b <- mustExec' i
      s' <- get
      put s' { execCache = HM.insert i b (execCache s') }
      return b

mustExec' :: Instruction -> AnalysisMonad Bool
mustExec' i = do
  cdg <- asks controlDepGraph
  dt <- asks domTree
  case controlDependencies cdg i of
    [] -> return True
    [_] -> do
      let Just bb = instructionBasicBlock i
          preds = basicBlockPredecessors (cdgCFG cdg) bb
          terms = map basicBlockTerminatorInstruction preds
          nonBackedges = filter (isNotBackedge dt i) terms

      return $! all isUnconditional nonBackedges
    _ -> return False
  where
    isUnconditional UnconditionalBranchInst {} = True
    isUnconditional _ = False
    isNotBackedge g inst br = not (dominates g inst br)

-- | At each Phi function, we can say that the Phi value is not null if
-- all of its incoming values are not null on their respective
-- branches.
--
-- Otherwise, if any incoming value may be NULL, the phi node is NULL
-- too.
--
-- We process all Phi instructions in parallel.  Each one corresponds
-- to one variable.  Our job here is to decide which phi variables are
-- definitely not null and to remove them from the null info (and mark
-- the rest as possibly null).
--
-- A phi node is considered to be not-null if all of its incoming
-- values that are Arguments are not-null on their respective
-- branches.  The rationale for this is that only Arguments are really
-- under the control of the caller; if the function checks the
-- argument against null and replaces null arguments with some other
-- value of its own, that means that it has some (intended) non-fatal
-- alternative behavior for null arguments.
nullPhiTransfer :: [Instruction] -> [(BasicBlock, NullInfo, CFGEdge)]
                   -> AnalysisMonad NullInfo
nullPhiTransfer phis incomingEdges = do
  let (newNotNullVals, newNullVals) = partition (phiIsNotNull incomingEdges) phis
      ni' = foldr (recordPossiblyNull . Value) ni newNullVals
  return $! foldr (recordNotNull . Value) ni' newNotNullVals
  where
    ni = meets $ map (\(_, i, _) -> i) incomingEdges
    phiIsNotNull es PhiNode { phiIncomingValues = pvs } =
      all (argNotNullOnIncoming es) pvs
    phiIsNotNull _ i = $err' ("Non-phi instruction: " ++ show i)

lookup3 :: (Eq a) => a -> [(a, b, c)] -> Maybe (a, b, c)
lookup3 k = find (\(k', _, _) -> k == k')

argNotNullOnIncoming :: [(BasicBlock, NullInfo, CFGEdge)]
                        -> (Value, Value)
                        -> Bool
argNotNullOnIncoming predOuts (v, bbv) =
  case valueContent' v of
    ArgumentC _ ->
      case valueContent bbv of
        BasicBlockC bb ->
          case bb `lookup3` predOuts of
            Nothing -> $err' ("No predecessor value for " ++ show bbv)
            Just (_, ni, e) ->
              let ni' = removeNonNullPointers ni [e]
                  isNull = v `S.member` mayBeNull ni'
              in not isNull
        _ -> $err' ("Not a basic block: " ++ show bbv)
    -- If it isn't an argument, don't count it against the phi node.
    -- Only arguments are provided by the caller.  If the value is not
    -- provided by the caller, assume that the library is doing
    -- something reasonable and safe internally.
    _ -> True

-- | Clobber the value of @ptr@ (mark it as possibly NULL due to
-- assignment).
maybeClobber :: NullInfo -> Value -> Value -> NullInfo
maybeClobber ni ptr _ {-newVal-} = recordPossiblyNull ptr ni

recordIfMayBeNull :: NullInfo -> Value -> AnalysisMonad NullInfo
recordIfMayBeNull ni ptr =
  -- If we don't get a base pointer, don't bother reasoning about this
  -- value.  Some values are always safe (allocas and globals are
  -- always valid pointers, even if the pointers they *contain* might
  -- not be).
  maybe (return ni) checkBase (memAccessBase ptr)
  where
    checkBase b =
      case b `S.member` mayBeNull ni of
        -- There was an explicit check to ensure that the pointer in
        -- this operation was not NULL, so we know for sure that it is
        -- safe.
        False -> return ni
        -- In this case, there was no explicit test for the pointer in
        -- use.  However, if this is a phi or select instruction then
        -- we might have some information about some of the incoming
        -- values that must not be NULL.  Do not report these known to
        -- be not-null pointers.
        --
        -- Again in the case of Phi nodes,
        True ->
          let nullVals = filter (`S.member` mayBeNull ni) (flattenValue b)
          in return $! foldl' addUncheckedAccess ni nullVals




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
  let ni' = ni { accessedUnchecked = accessedUnchecked ni `S.union` newUnchecked }
  in ni'
  where
    -- | FIXME: Here is the spot we need to pick out arguments
    args = case valueContent' ptr of
      ArgumentC a -> [Value a]
      _ -> []
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
--
-- If a Phi node (or Select) is checked against NULL, put that node in
-- the not-null set.  Later on, if there is a use of a phi node, any
-- of the values that the phi node could represent are guarded/not
-- guarded.
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
                        , cmpV1 = (valueContent' -> InstructionC v1@PhiNode {})
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
  InstructionC ICmpInst { cmpPredicate = ICmpEq
                        , cmpV2 = (valueContent' -> InstructionC v2@PhiNode {})
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
                        , cmpV1 = (valueContent' -> InstructionC v1@PhiNode{})
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
  InstructionC ICmpInst { cmpPredicate = ICmpNe
                        , cmpV2 = (valueContent' -> InstructionC v2@PhiNode{})
                        , cmpV1 = (valueContent -> ConstantC ConstantPointerNull {}) } ->
    process' ni (Value v2) (cond False)
  -- FIXME: Do we need these separate cases here?  We don't really
  -- care what type of value v1 and v2 are...

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
-}

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