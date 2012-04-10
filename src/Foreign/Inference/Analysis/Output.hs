{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TemplateHaskell #-}
-- | FIXME: Implement interprocedural info prop
module Foreign.Inference.Analysis.Output (
  -- * Interface
  OutputSummary,
  identifyOutput
  ) where

import Control.DeepSeq
import Data.HashSet ( HashSet )
import qualified Data.HashSet as HS
import Data.Lens.Common
import Data.Lens.Template
import Data.Map ( Map )
import qualified Data.Map as M
import Data.Set ( Set )
import qualified Data.Set as S
import Debug.Trace.LocationTH

import LLVM.Analysis
import LLVM.Analysis.CFG
import LLVM.Analysis.CallGraphSCCTraversal
import LLVM.Analysis.Dataflow

import Foreign.Inference.AnalysisMonad
import Foreign.Inference.Diagnostics
import Foreign.Inference.Interface

data ArgumentDirection = ArgIn
                       | ArgOut
                       | ArgBoth
                       deriving (Eq, Ord)

instance Show ArgumentDirection where
  show ArgIn = "in"
  show ArgOut = "out"
  show ArgBoth = "both"

instance NFData ArgumentDirection

type SummaryType = Map Argument (ArgumentDirection, [Witness])
data OutputSummary =
  OutputSummary { _outputSummary :: SummaryType
                , _outputDiagnostics :: Diagnostics
                }

$(makeLens ''OutputSummary)

instance Eq OutputSummary where
  (OutputSummary s1 _) == (OutputSummary s2 _) = s1 == s2

instance Monoid OutputSummary where
  mempty = OutputSummary mempty mempty
  mappend (OutputSummary s1 d1) (OutputSummary s2 d2) =
    OutputSummary (M.union s1 s2) (mappend d1 d2)

instance NFData OutputSummary where
  rnf o@(OutputSummary s d) = s `deepseq` d `deepseq` o `seq` ()

instance HasDiagnostics OutputSummary where
  diagnosticLens = outputDiagnostics

instance SummarizeModule OutputSummary where
  summarizeFunction _ _ = []
  summarizeArgument = summarizeOutArgument

summarizeOutArgument :: Argument -> OutputSummary -> [(ParamAnnotation, [Witness])]
summarizeOutArgument a (OutputSummary s _) =
  case M.lookup a s of
    Nothing -> []
    Just (ArgIn, _) -> []
    Just (ArgOut, ws) -> [(PAOut, ws)]
    Just (ArgBoth, ws) -> [(PAInOut, ws)]

data OutData = OD { moduleSummary :: OutputSummary
                  , dependencySummary :: DependencySummary
                  }

-- | Note that array parameters are not out parameters, so we rely on
-- the Array analysis to let us filter those parameters out of our
-- results.
identifyOutput :: (FuncLike funcLike, HasCFG funcLike, HasFunction funcLike)
                  => DependencySummary
                  -> Lens compositeSummary OutputSummary
                  -> ComposableAnalysis compositeSummary funcLike
identifyOutput ds lns =
  composableAnalysisM runner outAnalysis lns
  where
    runner a = runAnalysis a constData ()
    constData = OD mempty ds

data OutInfo = OI { outputInfo :: !(Map Argument (ArgumentDirection, Set Witness))
                  , aggregates :: !(HashSet Argument)
                  }
             deriving (Eq, Show)

instance MeetSemiLattice OutInfo where
  meet = meetOutInfo

instance MeetSemiLattice ArgumentDirection where
  meet ArgIn ArgIn = ArgIn
  meet ArgOut ArgOut = ArgOut
  meet ArgIn ArgOut = ArgBoth
  meet ArgOut ArgIn = ArgBoth
  meet ArgBoth _ = ArgBoth
  meet _ ArgBoth = ArgBoth

instance BoundedMeetSemiLattice OutInfo where
  top = OI M.empty HS.empty

meetOutInfo :: OutInfo -> OutInfo -> OutInfo
meetOutInfo (OI m1 s1) (OI m2 s2) =
  OI (M.unionWith meetWithWitness m1 m2) (s1 `HS.union` s2)
  where
    meetWithWitness (v1, w1) (v2, w2) = (meet v1 v2, S.union w1 w2)

instance DataflowAnalysis Analysis OutInfo where
  transfer = outTransfer

type Analysis = AnalysisMonad OutData ()

outAnalysis :: (FuncLike funcLike, HasFunction funcLike, HasCFG funcLike)
               => funcLike -> OutputSummary -> Analysis OutputSummary
outAnalysis funcLike s@(OutputSummary summ _) = do
  let envMod e = e { moduleSummary = s }
  funcInfo <- local envMod (forwardDataflow top funcLike)
  let exitInfo = map (dataflowResult funcInfo) (functionExitInstructions f)
      OI exitInfo' aggArgs = meets exitInfo
      exitInfo'' = M.filterWithKey (\k _ -> not (HS.member k aggArgs)) exitInfo'
      exitInfo''' = M.map (\(a, ws) -> (a, S.toList ws)) exitInfo''
  -- Merge the local information we just computed with the global
  -- summary.  Prefer the locally computed info if there are
  -- collisions (could arise while processing SCCs).
  return $! (outputSummary ^= M.union exitInfo''' summ) s
  where
    f = getFunction funcLike

-- | This transfer function only needs to be concerned with Load and
-- Store instructions (for now).  Loads add in an ArgIn value. Stores
-- add an ArgOut.
--
-- Note, we don't use valueContent' to strip bitcasts here since
-- accesses to bitfields use lots of interesting bitcasts and give us
-- false positives.
outTransfer :: OutInfo -> Instruction -> Analysis OutInfo
outTransfer info i =
  case i of
    LoadInst { loadAddress = (valueContent -> ArgumentC ptr) } ->
      return $! merge i ptr ArgIn info
    StoreInst { storeAddress = (valueContent -> ArgumentC ptr) } ->
      return $! merge i ptr ArgOut info
    AtomicRMWInst { atomicRMWPointer = (valueContent -> ArgumentC ptr) } ->
      return $! merge i ptr ArgIn info
    AtomicCmpXchgInst { atomicCmpXchgPointer = (valueContent -> ArgumentC ptr) } ->
      return $! merge i ptr ArgIn info

    -- We don't want to treat any aggregates as output parameters yet.
    -- Record all arguments used as aggregates and filter them out at
    -- the end of the analysis.
    --
    -- Later, we want to expand the definition of output parameters to
    -- cover structs where all fields are initialized.
    GetElementPtrInst { getElementPtrValue = (valueContent' -> ArgumentC ptr) } ->
      return $! info { aggregates = HS.insert ptr (aggregates info) }

    CallInst { callFunction = f, callArguments = args } ->
      callTransfer info i f (map fst args)
    InvokeInst { invokeFunction = f, invokeArguments = args }->
      callTransfer info i f (map fst args)

    _ -> return info

callTransfer :: OutInfo -> Instruction -> Value -> [Value] -> Analysis OutInfo
callTransfer info i f args = do
  let indexedArgs = zip [0..] args
  modSumm <- asks moduleSummary
  depSumm <- asks dependencySummary

  foldM (checkArg depSumm modSumm) info indexedArgs
  where
    checkArg ds ms acc (ix, arg) =
      case valueContent' arg of
        ArgumentC a ->
          case lookupArgumentSummary ds ms f ix of
            Nothing -> do
              let errMsg = "No summary for " ++ show (valueName f)
              emitWarning Nothing "OutputAnalysis" errMsg
              return acc
            Just attrs ->
              case PAOut `elem` attrs of
                True -> return $! merge i a ArgOut acc
                False -> return $! merge i a ArgIn acc
        _ -> return acc

merge :: Instruction -> Argument -> ArgumentDirection -> OutInfo -> OutInfo
merge i arg ArgBoth (OI oi a) =
  let ws = S.singleton (Witness i (show ArgBoth))
  in OI (M.insert arg (ArgBoth, ws) oi) a
merge i arg newVal info@(OI oi a) =
  case M.lookup arg oi of
    Nothing ->
      let ws = S.singleton (Witness i (show newVal))
      in OI (M.insert arg (newVal, ws) oi) a
    Just (ArgBoth, _) -> info
    Just (ArgOut, _) -> info
    Just (ArgIn, ws) ->
      case newVal of
        ArgOut ->
          let nw = Witness i (show ArgBoth)
          in OI (M.insert arg (ArgBoth, S.insert nw ws) oi) a
        ArgIn -> info
        ArgBoth -> $failure "Infeasible path"

removeArrayPtr :: Argument -> OutInfo -> OutInfo
removeArrayPtr a (OI oi ag) = OI (M.delete a oi) ag
