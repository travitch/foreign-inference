module Foreign.Inference.Analysis.Return (
  ReturnSummary,
  identifyReturns
  ) where

import Control.DeepSeq
import Control.Monad.Identity
import Data.Lens.Common
import Data.Monoid
import Data.HashSet ( HashSet )
import qualified Data.HashSet as S

import Data.LLVM
import Data.LLVM.Analysis.CFG
import Data.LLVM.Analysis.CallGraphSCCTraversal
import Data.LLVM.Analysis.NoReturn

import Foreign.Inference.AnalysisMonad
import Foreign.Inference.Interface

type SummaryType = HashSet Function
data ReturnSummary = ReturnSummary !SummaryType
                   deriving (Eq)

instance HasDiagnostics ReturnSummary

instance Monoid ReturnSummary where
  mempty = ReturnSummary mempty
  mappend (ReturnSummary s1) (ReturnSummary s2) =
    ReturnSummary (s1 `mappend` s2)

instance NFData ReturnSummary where
  rnf r@(ReturnSummary s) = s `deepseq` r `seq` ()

instance SummarizeModule ReturnSummary where
  summarizeFunction f (ReturnSummary summ) =
    case f `S.member` summ of
      False -> []
      True -> [FANoRet]
  summarizeArgument _ _ = []
{-
-- | Never produces diagnostics, but the value is included for
-- consistency.
identifyReturns :: DependencySummary -> CallGraph -> ReturnSummary
identifyReturns ds cg = ReturnSummary $
  parallelCallGraphSCCTraversal cg analysisFunction mempty
  where
    analysisFunction = callGraphAnalysisM runIdentity (noReturnAnalysis extSumm)
    extSumm ef =
      case lookupFunctionSummary ds ef of
        Nothing -> return False
        Just s -> return $ FANoRet `elem` s
-}
identifyReturns :: (FuncLike funcLike, HasCFG funcLike)
                   => DependencySummary
                   -> Lens compositeSummary ReturnSummary
                   -> ComposableAnalysis compositeSummary funcLike
identifyReturns ds lns =
  monadicComposableAnalysis runIdentity analysisWrapper lns
  where
    analysisWrapper f (ReturnSummary s) = do
      res <- noReturnAnalysis extSumm f s
      return $! ReturnSummary res
    extSumm ef =
      case lookupFunctionSummary ds ef of
        Nothing -> return False
        Just s -> return $ FANoRet `elem` s