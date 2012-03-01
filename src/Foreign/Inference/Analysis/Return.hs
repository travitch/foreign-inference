module Foreign.Inference.Analysis.Return (
  ReturnSummary,
  identifyReturns
  ) where

import Control.DeepSeq
import Control.Monad.Identity
import Data.Monoid
import Data.HashSet ( HashSet )
import qualified Data.HashSet as S

import Data.LLVM
import Data.LLVM.Analysis.CallGraph
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

-- | Never produces diagnostics, but the value is included for
-- consistency.
identifyReturns :: DependencySummary -> CallGraph -> ReturnSummary
identifyReturns ds cg = ReturnSummary $
  parallelCallGraphSCCTraversal cg runIdentity (noReturnAnalysis extSumm) mempty
  where
    extSumm ef =
      case lookupFunctionSummary ds ef of
        Nothing -> return False
        Just s -> return $ FANoRet `elem` s
