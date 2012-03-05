{-|

1) Identify functions of 1 parameter that conditionally call a finalizer.

2) The condition should compare a value reachable from the argument
   against zero or one (record the access path)

3) Identify functions of one parameter incrementing something
   accessible via that same access path

-}
module Foreign.Inference.Analysis.RefCount where

import Control.DeepSeq
import Data.HashSet ( HashSet )
import qualified Data.HashSet as S
import Data.Monoid

import LLVM.Analysis
import LLVM.Analysis.CFG
import LLVM.Analysis.CallGraphSCCTraversal

import Foreign.Inference.AnalysisMonad
import Foreign.Inference.Analysis.Finalize
import Foreign.Inference.Analysis.Util.AccessPath
import Foreign.Inference.Diagnostics
import Foreign.Inference.Interface

data RefCountSummary =
  RefCountSummary { conditionalFinalizers :: HashSet Function
                  , refCountDiagnostics :: !Diagnostics
                  }

instance Monoid RefCountSummary where
  mempty = RefCountSummary mempty mempty
  mappend (RefCountSummary s1 d1) (RefCountSummary s2 d2) =
    RefCountSummary (s1 `mappend` s2) (d1 `mappend` d2)

instance NFData RefCountSummary where
  rnf r@(RefCountSummary s _) = s `deepseq` r `seq` ()

instance Eq RefCountSummary where
  (RefCountSummary s1 _) == (RefCountSummary s2 _) = s1 == s2

instance HasDiagnostics RefCountSummary where
  addDiagnostics s d =
    s { refCountDiagnostics = refCountDiagnostics s `mappend` d }
  getDiagnostics = refCountDiagnostics

data RefCountData =
  RefCountData DependencySummary

type Analysis = AnalysisMonad RefCountData ()

identifyRefCounting :: (FuncLike funcLike, HasFunction funcLike, HasCFG funcLike)
                       => DependencySummary
                       -> Lens compositeSummary RefCountSummary
                       -> Lens compositeSummary FinalizerSummary
                       -> ComposableAnalysis compositeSummary funcLike
identifyRefCounting ds lns depLens =
  composableDependencyAnalysisM runner refCountAnalysis lns depLens
  where
    runner a = runAnalysis a constData ()
    constData = RefCountData ds

refCountAnalysis :: (FuncLike funcLike, HasCFG funcLike, HasFunction funcLike)
                    => FinalizerSummary
                    -> funcLike
                    -> RefCountSummary
                    -> Analysis RefCountSummary
refCountAnalysis finSumm funcLike summ = return summ