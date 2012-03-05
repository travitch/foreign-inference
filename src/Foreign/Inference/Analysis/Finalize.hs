{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses #-}
{-# LANGUAGE ViewPatterns #-}
-- | Identify function arguments that are *finalized*.  An argument is
-- finalized if, on every path, it is passed as a parameter to a
-- function that finalizes it *or* the argument is NULL.
--
-- The dataflow fact is a bit per argument that, if set, indicates
-- that the argument is neither finalized nor null.  The meet operator
-- is bitwise or.  This is actually implemented with sets and union.
-- The finalized arguments are those that are *NOT* in the set at the
-- end of the function.  This function need only consider normal
-- returns.  Functions with an unreachable return (due to exit,
-- longjmp, etc) are not finalizers.
module Foreign.Inference.Analysis.Finalize (
  FinalizerSummary,
  identifyFinalizers,
  -- * Testing
  finalizerSummaryToTestFormat
  ) where

import Control.DeepSeq
import Data.HashMap.Strict ( HashMap )
import qualified Data.HashMap.Strict as HM
import Data.HashSet ( HashSet )
import qualified Data.HashSet as HS
import Data.Lens.Common
import Data.Map ( Map )
import qualified Data.Map as M
import Data.Set ( Set )
import qualified Data.Set as S

import LLVM.Analysis
import LLVM.Analysis.CFG
import LLVM.Analysis.CallGraphSCCTraversal
import LLVM.Analysis.Dataflow

import Foreign.Inference.AnalysisMonad
import Foreign.Inference.Diagnostics
import Foreign.Inference.Interface

-- import Text.Printf
-- import Debug.Trace
-- debug = flip trace

-- | If an argument is finalized, it will be in the map with its
-- associated witnesses.  If no witnesses could be identified, the
-- witness list will simply be empty.
type SummaryType = HashMap Argument [Witness]
data FinalizerSummary =
  FinalizerSummary { finalizerSummary :: SummaryType
                   , finalizerDiagnostics :: Diagnostics
                   }

instance Eq FinalizerSummary where
  (FinalizerSummary s1 _) == (FinalizerSummary s2 _) = s1 == s2

instance Monoid FinalizerSummary where
  mempty = FinalizerSummary mempty mempty
  mappend (FinalizerSummary s1 d1) (FinalizerSummary s2 d2) =
    FinalizerSummary (HM.unionWith merge s1 s2) (mappend d1 d2)
    where
      merge l1 l2 = S.toList $ S.union (S.fromList l1) (S.fromList l2)

instance NFData FinalizerSummary where
  rnf f@(FinalizerSummary s d) = s `deepseq` d `deepseq` f `seq` ()

instance HasDiagnostics FinalizerSummary where
  addDiagnostics s d =
    s { finalizerDiagnostics = finalizerDiagnostics s `mappend` d }
  getDiagnostics = finalizerDiagnostics

instance SummarizeModule FinalizerSummary where
  summarizeFunction _ _ = []
  summarizeArgument = summarizeFinalizerArgument

summarizeFinalizerArgument :: Argument
                              -> FinalizerSummary
                              -> [(ParamAnnotation, [Witness])]
summarizeFinalizerArgument a (FinalizerSummary m _) =
  case HM.lookup a m of
    Nothing -> []
    Just ws -> [(PAFinalize, ws)]

data FinalizerData =
  FinalizerData { moduleSummary :: SummaryType
                , dependencySummary :: DependencySummary
                }

identifyFinalizers :: (FuncLike funcLike, HasFunction funcLike, HasCFG funcLike)
                      => DependencySummary
                      -> Lens compositeSummary FinalizerSummary
                      -> ComposableAnalysis compositeSummary funcLike
identifyFinalizers ds lns =
  composableAnalysisM runner finalizerAnalysis lns
  where
    runner a = runAnalysis a constData ()
    constData = FinalizerData HM.empty ds

data FinalizerInfo =
  FinalizerInfo { notFinalizedOrNull :: HashSet Argument
                , finalizedWitnesses :: HashMap Argument (Set Witness)
                }
  deriving (Eq, Show)

instance MeetSemiLattice FinalizerInfo where
  meet (FinalizerInfo s1 m1) (FinalizerInfo s2 m2) =
    FinalizerInfo { notFinalizedOrNull = HS.union s1 s2
                  , finalizedWitnesses = HM.unionWith S.union m1 m2
                  }

instance BoundedMeetSemiLattice FinalizerInfo where
  top = FinalizerInfo HS.empty HM.empty

type Analysis = AnalysisMonad FinalizerData ()

instance DataflowAnalysis Analysis FinalizerInfo where
  transfer = finalizerTransfer
  edgeTransfer = finalizerEdgeTransfer

finalizerAnalysis :: (FuncLike funcLike, HasFunction funcLike, HasCFG funcLike)
                     => funcLike -> FinalizerSummary -> Analysis FinalizerSummary
finalizerAnalysis funcLike s@(FinalizerSummary summ _) = do
  -- Update the immutable data with the information we have gathered
  -- from the rest of the module so far.  We want to be able to access
  -- this in the Reader environment
  let envMod e = e { moduleSummary = summ }
      set0 = HS.fromList $ filter isPointer (functionParameters f)
      fact0 = FinalizerInfo set0 HM.empty

  funcInfo <- local envMod (forwardDataflow fact0 funcLike)

  let exitInsts = functionExitInstructions f
      exitInfo = map (dataflowResult funcInfo) exitInsts
      FinalizerInfo notFinalized witnesses = meets exitInfo
  -- The finalized parameters are those that are *NOT* in our fact set
  -- at the return instruction
      finalizedOrNull = set0 `HS.difference` notFinalized
      attachWitness a m = HM.insert a (S.toList (HM.lookupDefault S.empty a witnesses)) m
      newInfo = HS.foldr attachWitness HM.empty finalizedOrNull
  -- Note, we perform the union with newInfo first so that any
  -- repeated keys take their value from what we just computed.  This
  -- is important for processing SCCs in the call graph, where a
  -- function may be visited more than once.  We always want the most
  -- up-to-date info.
  return $! s { finalizerSummary = newInfo `HM.union` summ }
  where
    f = getFunction funcLike

finalizerEdgeTransfer :: FinalizerInfo -> CFGEdge -> Analysis FinalizerInfo
finalizerEdgeTransfer fi (TrueEdge v) = return $! processCFGEdge fi not v
finalizerEdgeTransfer fi (FalseEdge v) = return $! processCFGEdge fi id v
finalizerEdgeTransfer fi _ = return fi

finalizerTransfer :: FinalizerInfo -> Instruction -> Analysis FinalizerInfo
finalizerTransfer info i =
  case i of
    CallInst { callFunction = calledFunc, callArguments = args } ->
      callTransfer i (stripBitcasts calledFunc) (map fst args) info
    InvokeInst { invokeFunction = calledFunc, invokeArguments = args } ->
      callTransfer i (stripBitcasts calledFunc) (map fst args) info
    _ -> return info

callTransfer :: Instruction -> Value -> [Value] -> FinalizerInfo -> Analysis FinalizerInfo
callTransfer i v as info =
  case valueContent' v of
    FunctionC f -> do
      modSum <- asks moduleSummary
      let indexedArgs = zip [0..] as
      foldM (checkInternalArg i modSum f) info indexedArgs
    ExternalFunctionC f -> do
      depSum <- asks dependencySummary
      let indexedArgs = zip [0..] as
      foldM (checkExternalArg i depSum f) info indexedArgs

    -- Indirect call - no point in resolving it since we aren't
    -- getting any useful information.
    _ -> return info

checkInternalArg :: Instruction -> SummaryType -> Function
                    -> FinalizerInfo -> (Int, Value) -> Analysis FinalizerInfo
checkInternalArg i summ f info (ix, (valueContent' -> ArgumentC a)) =
  case functionIsVararg f && ix >= length formals of
    -- Pointer passed as a vararg, no information
    True -> return info
    False ->
      -- If the formal corresponding to this actual is in the summary map,
      -- it is finalized (and so is @a@ on this path).
      case HM.lookup (formals !! ix) summ of
        Nothing -> return info
        Just _ -> return $! removeArgWithWitness a i "finalized" info
  where
    formals = functionParameters f
checkInternalArg _ _ _ info _ = return info

checkExternalArg :: Instruction -> DependencySummary -> ExternalFunction
                    -> FinalizerInfo -> (Int, Value) -> Analysis FinalizerInfo
checkExternalArg i summ f info (ix, (valueContent' -> ArgumentC a)) =
  case lookupArgumentSummary summ f ix of
    Nothing -> do
      emitWarning Nothing "FinalizerAnalysis" errMsg
      return info
    Just attrs ->
      case PAFinalize `elem` attrs of
        False -> return info
        True -> return $! removeArgWithWitness a i "finalized" info
  where
    errMsg = "No ExternalFunction summary for " ++ show (externalFunctionName f)
checkExternalArg _ _ _ info _ = return info

removeArgWithWitness :: Argument -> Instruction -> String -> FinalizerInfo -> FinalizerInfo
removeArgWithWitness a i reason (FinalizerInfo s m) =
  let w = Witness i reason
  in FinalizerInfo { notFinalizedOrNull = HS.delete a s
                   , finalizedWitnesses = HM.insertWith S.union a (S.singleton w) m
                   }

-- | If we know, based on some incoming CFG edges, that an argument is
-- NULL, remove it from the current set and add the comparison or
-- branch instruction to the witness set for that argument.
processCFGEdge :: FinalizerInfo -> (Bool -> Bool) -> Value -> FinalizerInfo
processCFGEdge fi cond v =
  case valueContent v of
    InstructionC i@ICmpInst { cmpPredicate = ICmpEq
                            , cmpV1 = (valueContent' -> ArgumentC v1)
                            , cmpV2 = (valueContent -> ConstantC ConstantPointerNull {}) } ->
      process' i fi v1 (cond True)
    InstructionC i@ICmpInst { cmpPredicate = ICmpEq
                            , cmpV2 = (valueContent' -> ArgumentC v2)
                            , cmpV1 = (valueContent -> ConstantC ConstantPointerNull {}) } ->
      process' i fi v2 (cond True)
    InstructionC i@ICmpInst { cmpPredicate = ICmpNe
                            , cmpV1 = (valueContent' -> ArgumentC v1)
                            , cmpV2 = (valueContent -> ConstantC ConstantPointerNull {}) } ->
      process' i fi v1 (cond False)
    InstructionC i@ICmpInst { cmpPredicate = ICmpNe
                            , cmpV2 = (valueContent' -> ArgumentC v2)
                            , cmpV1 = (valueContent -> ConstantC ConstantPointerNull {}) } ->
      process' i fi v2 (cond False)
    _ -> fi

process' :: Instruction -> FinalizerInfo -> Argument -> Bool -> FinalizerInfo
process' i fi arg isNull =
  case isNull of
    True -> fi
    False -> removeArgWithWitness arg i "null" fi

-- Helpers

isPointer :: (IsValue a) => a -> Bool
isPointer v =
  case valueType v of
    TypePointer _ _ -> True
    _ -> False


-- Testing

finalizerSummaryToTestFormat :: FinalizerSummary -> Map String (Set String)
finalizerSummaryToTestFormat (FinalizerSummary m _) = convert m
  where
    convert = foldr addElt M.empty . map toFuncNamePair . HM.keys
    addElt (f, a) = M.insertWith' S.union f (S.singleton a)
    toFuncNamePair arg =
      let f = argumentFunction arg
      in (show (functionName f), show (argumentName arg))
