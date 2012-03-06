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

import Control.Arrow
import Control.DeepSeq
import Data.Map ( Map )
import qualified Data.Map as M
import Data.Set ( Set )
import qualified Data.Set as S
import Data.HashMap.Strict ( HashMap )
import Data.Lens.Common
import Data.Lens.Template
import qualified Data.HashMap.Strict as HM
import Data.Maybe ( isJust )
import Data.Monoid
import FileLocation

import LLVM.Analysis
import LLVM.Analysis.CDG
import LLVM.Analysis.CFG
import LLVM.Analysis.CallGraphSCCTraversal
import LLVM.Analysis.Dataflow
import LLVM.Analysis.Dominance

import Foreign.Inference.Diagnostics
import Foreign.Inference.Interface
import Foreign.Inference.AnalysisMonad
import Foreign.Inference.Analysis.Return

-- import Text.Printf
-- import Debug.Trace

-- debug' :: c -> String -> c
-- debug' = flip trace

type SummaryType = HashMap Argument [Witness]

-- | Note, this could be a Set (Argument, Instruction) where the
-- Instruction is the fact we saw that led us to believe that Argument
-- is not nullable.
data NullableSummary =
  NullableSummary { _nullableSummary :: !SummaryType
                  , _nullableDiagnostics :: !Diagnostics
                  }

$(makeLens ''NullableSummary)

instance Monoid NullableSummary where
  mempty = NullableSummary mempty mempty
  mappend (NullableSummary s1 d1) (NullableSummary s2 d2) =
    NullableSummary (s1 `mappend` s2) (d1 `mappend` d2)

instance NFData NullableSummary where
  rnf n@(NullableSummary s d) = d `deepseq` s `deepseq` n `seq` ()

instance Eq NullableSummary where
  (NullableSummary s1 _) == (NullableSummary s2 _) = s1 == s2

instance SummarizeModule NullableSummary where
  summarizeFunction _ _ = []
  summarizeArgument = summarizeNullArgument

summarizeNullArgument :: Argument -> NullableSummary -> [(ParamAnnotation, [Witness])]
summarizeNullArgument a (NullableSummary s _) =
  case HM.lookup a s of
    Nothing -> []
    Just ws -> [(PANotNull, ws)]

identifyNullable :: (FuncLike funcLike, HasFunction funcLike, HasCFG funcLike)
                    => DependencySummary
                    -> Lens compositeSummary NullableSummary
                    -> Lens compositeSummary ReturnSummary
                    -> ComposableAnalysis compositeSummary funcLike
identifyNullable ds lns depLens =
  composableDependencyAnalysisM runner nullableAnalysis lns depLens
  where
    runner a = runAnalysis a constData cache
    constData = ND HM.empty ds undefined undefined undefined
    cache = NState HM.empty

data NullData = ND { moduleSummary :: SummaryType
                   , dependencySummary :: DependencySummary
                   , returnSummary :: ReturnSummary
                   , controlDepGraph :: CDG
                   , domTree :: DominatorTree
                   }

data NullState = NState { phiCache :: HashMap Instruction (Maybe Value) }

data NullInfo = NInfo { nullArguments :: Set Argument
                      , nullWitnesses :: Map Argument (Set Witness)
                      }
              deriving (Eq, Ord, Show)

instance MeetSemiLattice NullInfo where
  meet = meetNullInfo

instance BoundedMeetSemiLattice NullInfo where
  top = NInfo S.empty M.empty

instance HasDiagnostics NullableSummary where
  diagnosticLens = nullableDiagnostics

type Analysis = AnalysisMonad NullData NullState
instance DataflowAnalysis Analysis NullInfo where
  transfer = nullTransfer
  edgeTransfer = nullEdgeTransfer

meetNullInfo :: NullInfo -> NullInfo -> NullInfo
meetNullInfo ni1 ni2 =
  NInfo { nullArguments = nullArguments ni1 `S.union` nullArguments ni2
        , nullWitnesses = M.unionWith S.union (nullWitnesses ni1) (nullWitnesses ni2)
        }

-- | The analysis that is applied to every function in the call graph.
-- It runs a dataflow analysis over the function to identify the
-- parameters that are used before they are known to be non-NULL.
--
-- This set of arguments is added to the global summary data (set of
-- all non-nullable arguments).
nullableAnalysis :: (FuncLike funcLike, HasCFG funcLike, HasFunction funcLike)
                    => ReturnSummary
                    -> funcLike
                    -> NullableSummary
                    -> Analysis NullableSummary
nullableAnalysis retSumm funcLike s@(NullableSummary summ _) = do
  -- Run this sub-analysis step with a modified environment - the
  -- summary component is the current module summary (given to us by
  -- the SCC traversal).
  --
  -- The initial state of the dataflow analysis is top -- all pointer
  -- parameters are NULLable.
  let envMod e = e { moduleSummary = summ
                   , returnSummary = retSumm
                   , controlDepGraph = controlDependenceGraph cfg
                   , domTree = dominatorTree cfg
                   }
      args = filter isPointer (functionParameters f)
      fact0 = top { nullArguments = S.fromList args }
  localInfo <- local envMod (forwardDataflow fact0 funcLike)

  let exitInfo = map (dataflowResult localInfo) (functionExitInstructions f)
      exitInfo' = meets exitInfo
      notNullableArgs = S.toList $ S.fromList args `S.difference` nullArguments exitInfo'
      argsAndWitnesses =
        map (attachWitness (nullWitnesses exitInfo')) notNullableArgs

  -- Update the module symmary with the set of pointer parameters that
  -- we have proven are accessed unchecked.
  let newSumm = foldr (\(a, ws) acc -> HM.insert a ws acc) summ argsAndWitnesses
  return $! (nullableSummary ^= newSumm) s
  where
    cfg = getCFG funcLike
    f = getFunction funcLike

attachWitness :: Map Argument (Set Witness)
                 -> Argument
                 -> (Argument, [Witness])
attachWitness m a =
  case M.lookup a m of
    Nothing -> (a, [])
    Just is -> (a, S.toList is)

nullEdgeTransfer :: NullInfo -> CFGEdge -> Analysis NullInfo
nullEdgeTransfer ni (TrueEdge v) = return $! processCFGEdge ni id v
nullEdgeTransfer ni (FalseEdge v) = return $! processCFGEdge ni not v
nullEdgeTransfer ni _ = return ni

-- | First, process the incoming CFG edges to learn about pointers
-- that are known to be non-NULL.  Then use this updated information
-- to identify pointers that are dereferenced when they *might* be
-- NULL.  Also map these possibly-NULL pointers to any corresponding
-- parameters.
nullTransfer :: NullInfo -> Instruction -> Analysis NullInfo
nullTransfer ni i =
  case i of
    LoadInst { loadAddress = ptr } ->
      valueDereferenced i ptr ni
    StoreInst { storeAddress = ptr } ->
      valueDereferenced i ptr ni
    AtomicRMWInst { atomicRMWPointer = ptr } ->
      valueDereferenced i ptr ni
    AtomicCmpXchgInst { atomicCmpXchgPointer = ptr } ->
      valueDereferenced i ptr ni

    CallInst { callFunction = calledFunc, callArguments = args } ->
      callTransfer i (stripBitcasts calledFunc) (map fst args) ni
    InvokeInst { invokeFunction = calledFunc, invokeArguments = args } ->
      callTransfer i (stripBitcasts calledFunc) (map fst args) ni

    _ -> return ni

valueDereferenced :: Instruction -> Value -> NullInfo -> Analysis NullInfo
valueDereferenced i ptr ni =
  case memAccessBase ptr of
    Nothing -> return ni
    Just v -> do
      v' <- mustExecuteValue v
      case v' of
        Nothing -> return ni
        Just mustVal ->
          case valueContent' mustVal of
            ArgumentC a ->
              case a `S.member` args of
                -- Already removed, no new info
                False -> return ni
                True ->
                  return ni { nullArguments = S.delete a args
                            , nullWitnesses =
                                 let w = Witness i "deref"
                                 in M.insertWith' S.union a (S.singleton w) ws
                            }
            _ -> return ni
  where
    args = nullArguments ni
    ws = nullWitnesses ni

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
callTransfer ::  Instruction
                 -> Value
                 -> [Value]
                 -> NullInfo
                 -> Analysis NullInfo
callTransfer i calledFunc args ni = do
  ni' <- case valueContent' calledFunc of
    FunctionC f ->do
      summ <- asks moduleSummary
      retSumm <- asks returnSummary
      case FANoRet `elem` summarizeFunction f retSumm of
        False -> definedFunctionTransfer i summ f ni args
        True ->
          return ni { nullArguments = S.empty
                    , nullWitnesses =
                      S.foldl' (addWitness i) (nullWitnesses ni) (nullArguments ni)
                    }
    ExternalFunctionC e ->  do
      summ <- asks dependencySummary
      case lookupFunctionSummary summ e of
        Nothing -> externalFunctionTransfer i summ e ni args
        Just s -> case FANoRet `elem` s of
          True ->
            return ni { nullArguments = S.empty
                      , nullWitnesses =
                        S.foldl' (addWitness i) (nullWitnesses ni) (nullArguments ni)
                      }
          False -> externalFunctionTransfer i summ e ni args
    _ -> return ni
  -- We also learn information about pointers that are not null if
  -- this is a call through a function pointer (calling a NULL
  -- function pointer is illegal)
  case isIndirectCallee calledFunc of
    False -> return ni'
    True -> valueDereferenced i calledFunc ni'

addWitness :: Instruction
              -> Map Argument (Set Witness)
              -> Argument
              -> Map Argument (Set Witness)
addWitness i m a = M.insertWith' S.union a (S.singleton (Witness i "arg")) m

isIndirectCallee :: Value -> Bool
isIndirectCallee val =
  case valueContent' val of
    FunctionC _ -> False
    ExternalFunctionC _ -> False
    _ -> True

definedFunctionTransfer :: Instruction -> SummaryType -> Function
                           -> NullInfo -> [Value] -> Analysis NullInfo
definedFunctionTransfer i summ f ni args =
  foldM markArgNotNullable ni indexedNotNullArgs
  where
    formals = functionParameters f
    notNullableArgs = filter (\frml -> isJust (HM.lookup frml summ)) formals
    isNotNullable (a, _) = not . null $ filter (==a) notNullableArgs
    -- | Pairs of not-nullable formals/actuals
    indexedNotNullArgs = filter isNotNullable $ zip formals args
    markArgNotNullable info (_, a) =
      valueDereferenced i a info

externalFunctionTransfer :: Instruction -> DependencySummary -> ExternalFunction
                            -> NullInfo -> [Value] -> Analysis NullInfo
externalFunctionTransfer i summ e ni args =
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
          True -> valueDereferenced i arg info

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
mustExecuteValue :: Value -> Analysis (Maybe Value)
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

mustExec' :: Instruction -> [(Value, Value)] -> Analysis (Maybe Value)
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
    _ -> return Nothing
  where
    toBB v =
      case valueContent v of
        BasicBlockC bb -> bb
        _ -> $err' ("Expected basic block: " ++ show v)
    isUnconditional UnconditionalBranchInst {} = True
    isUnconditional _ = False
    isNotBackedge g inst (_, br) = not (dominates g inst br)

isPointer :: (IsValue v) => v -> Bool
isPointer v = case valueType v of
  TypePointer _ _ -> True
  _ -> False

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
                        , cmpV1 = (valueContent' -> ArgumentC v1)
                        , cmpV2 = (valueContent -> ConstantC ConstantPointerNull {}) } ->
    process' ni v1 (cond True)
  InstructionC ICmpInst { cmpPredicate = ICmpEq
                        , cmpV2 = (valueContent' -> ArgumentC v2)
                        , cmpV1 = (valueContent -> ConstantC ConstantPointerNull {}) } ->
    process' ni v2 (cond True)
  InstructionC ICmpInst { cmpPredicate = ICmpNe
                        , cmpV1 = (valueContent' -> ArgumentC v1)
                        , cmpV2 = (valueContent -> ConstantC ConstantPointerNull {}) } ->
    process' ni v1 (cond False)
  InstructionC ICmpInst { cmpPredicate = ICmpNe
                        , cmpV2 = (valueContent' -> ArgumentC v2)
                        , cmpV1 = (valueContent -> ConstantC ConstantPointerNull {}) } ->
    process' ni v2 (cond False)
  _ -> ni

process' :: NullInfo -> Argument -> Bool -> NullInfo
process' ni arg isNull =
  case isNull of
    True -> ni
    False -> ni { nullArguments = arg `S.delete` nullArguments ni }

-- Testing

-- | Convert the 'NullableSummary' to a format that is easy to read
-- from a file for testing purposes.
nullSummaryToTestFormat :: NullableSummary -> Map String (Set String)
nullSummaryToTestFormat (NullableSummary m _) =
  foldr addArg M.empty (HM.toList m)
  where
    addArg (a, _) acc =
      let f = argumentFunction a
          k = show (functionName f)
          v = S.singleton (show (argumentName a))
      in M.insertWith' S.union k v acc
