{-# LANGUAGE RankNTypes, DeriveGeneric #-}
-- | This analysis identifies functions that never return.
--
-- These are functions that are guaranteed to never return because
-- they call exit on every path (or always go into an infinite loop).
--
-- This analysis is mostly used by the nullable pointer analysis.
module Foreign.Inference.Analysis.Return (
  ReturnSummary,
  identifyReturns
  ) where

import GHC.Generics ( Generic )

import Control.DeepSeq
import Control.DeepSeq.Generics ( genericRnf )
import Control.Lens ( Lens' )
import Data.Monoid
import Data.HashSet ( HashSet )
import qualified Data.HashSet as S

import LLVM.Analysis
import LLVM.Analysis.CFG
import LLVM.Analysis.CallGraphSCCTraversal
import LLVM.Analysis.NoReturn

import Foreign.Inference.Diagnostics
import Foreign.Inference.Interface
import Foreign.Inference.AnalysisMonad

type SummaryType = HashSet Function
data ReturnSummary = ReturnSummary !SummaryType
                   deriving (Eq, Generic)

instance HasDiagnostics ReturnSummary

instance Monoid ReturnSummary where
  mempty = ReturnSummary mempty
  mappend (ReturnSummary s1) (ReturnSummary s2) =
    ReturnSummary (s1 `mappend` s2)

instance NFData ReturnSummary where
  rnf = genericRnf

instance SummarizeModule ReturnSummary where
  summarizeFunction f (ReturnSummary summ) =
    case f `S.member` summ of
      False -> []
      True -> [(FANoRet, [])]
  summarizeArgument _ _ = []

type Analysis = AnalysisMonad () ()

identifyReturns :: (FuncLike funcLike, HasCFG funcLike)
                   => DependencySummary
                   -> Lens' compositeSummary ReturnSummary
                   -> ComposableAnalysis compositeSummary funcLike
identifyReturns ds lns =
  composableAnalysisM runner analysisWrapper lns
  where
    runner a = runAnalysis a ds () ()
    analysisWrapper f rs@(ReturnSummary s) = do
      res <- noReturnAnalysis (extSumm rs) f s
      return $! ReturnSummary res
    extSumm :: ReturnSummary -> ExternalFunction -> Analysis Bool
    extSumm rs ef = do
      summ <- lookupFunctionSummary rs ef
      case summ of
        Nothing -> return False
        Just s -> return $ FANoRet `elem` s
