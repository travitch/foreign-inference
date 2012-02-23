{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TemplateHaskell #-}
-- | FIXME: Implement interprocedural info prop
module Foreign.Inference.Analysis.Output (
  -- * Interface
  OutputSummary,
  identifyOutput
  ) where

import Control.Monad.RWS.Strict
import Data.HashSet ( HashSet )
import qualified Data.HashSet as HS
import Data.Map ( Map )
import qualified Data.Map as M
import Data.Set ( Set )
import qualified Data.Set as S
import FileLocation

import Data.LLVM
import Data.LLVM.Analysis.CallGraph
import Data.LLVM.Analysis.CallGraphSCCTraversal
import Data.LLVM.Analysis.Dataflow

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

type SummaryType = Map Argument (ArgumentDirection, [Witness])
data OutputSummary = OS SummaryType

instance Eq OutputSummary where
  (OS s1) == (OS s2) = s1 == s2

instance SummarizeModule OutputSummary where
  summarizeFunction _ _ = []
  summarizeArgument = summarizeOutArgument

summarizeOutArgument :: Argument -> OutputSummary -> [(ParamAnnotation, [Witness])]
summarizeOutArgument a (OS s) =
  case M.lookup a s of
    Nothing -> []
    Just (ArgIn, _) -> []
    Just (ArgOut, ws) -> [(PAOut, ws)]
    Just (ArgBoth, ws) -> [(PAInOut, ws)]

data OutData = OD { moduleSummary :: SummaryType
                  , dependencySummary :: DependencySummary
                  , callGraph :: CallGraph
                  }

-- | Note that array parameters are not out parameters, so we rely on
-- the Array analysis to let us filter those parameters out of our
-- results.
identifyOutput :: DependencySummary -> CallGraph
                  -> (OutputSummary, Diagnostics)
identifyOutput ds cg = (OS res, diags)
  where
    s0 = M.empty
    analysis = callGraphSCCTraversal cg outAnalysis s0
    constData = OD M.empty ds cg
    (res, diags) = evalRWS analysis constData ()

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

instance DataflowAnalysis AnalysisMonad OutInfo where
  transfer = outTransfer

type AnalysisMonad = RWS OutData Diagnostics ()

outAnalysis :: Function -> SummaryType -> AnalysisMonad SummaryType
outAnalysis f summ = do
  let envMod e = e { moduleSummary = summ }
  funcInfo <- local envMod (forwardDataflow top f)
  let exitInfo = map (dataflowResult funcInfo) (functionExitInstructions f)
      OI exitInfo' aggArgs = meets exitInfo
      exitInfo'' = M.filterWithKey (\k _ -> not (HS.member k aggArgs)) exitInfo'
      exitInfo''' = M.map (\(a, ws) -> (a, S.toList ws)) exitInfo''
  -- Merge the local information we just computed with the global
  -- summary.  Prefer the locally computed info if there are
  -- collisions (could arise while processing SCCs).
  return $! M.union exitInfo''' summ

-- | This transfer function only needs to be concerned with Load and
-- Store instructions (for now).  Loads add in an ArgIn value. Stores
-- add an ArgOut.
--
-- Note, we don't use valueContent' to strip bitcasts here since
-- accesses to bitfields use lots of interesting bitcasts and give us
-- false positives.
outTransfer :: OutInfo -> Instruction -> AnalysisMonad OutInfo
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

    _ -> return info

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
        ArgBoth -> $err' "Infeasible path"

removeArrayPtr :: Argument -> OutInfo -> OutInfo
removeArrayPtr a (OI oi ag) = OI (M.delete a oi) ag
