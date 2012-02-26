module Foreign.Inference.Analysis.Return (
  ReturnSummary,
  identifyReturns
  ) where

import Control.Monad.Identity
import Data.Monoid
import Data.Set ( Set )
import qualified Data.Set as S

import Data.LLVM
import Data.LLVM.Analysis.CallGraph
import Data.LLVM.Analysis.NoReturn

import Foreign.Inference.Diagnostics
import Foreign.Inference.Interface

type SummaryType = Set Function
data ReturnSummary = RS !SummaryType

instance SummarizeModule ReturnSummary where
  summarizeFunction f (RS summ) =
    case f `S.member` summ of
      False -> []
      True -> [FANoRet]
  summarizeArgument _ _ = []

-- | Never produces diagnostics, but the value is included for
-- consistency.
identifyReturns :: DependencySummary -> CallGraph -> (ReturnSummary, Diagnostics)
identifyReturns ds cg = (RS (S.fromList noRetFuncs), mempty)
  where
    noRetFuncs = runIdentity (noReturnAnalysis cg extSumm)
    extSumm ef = do
      let summ = lookupFunctionSummary ds ef
      case lookupFunctionSummary ds ef of
        Nothing -> return False
        Just s -> return $ FANoRet `elem` s
