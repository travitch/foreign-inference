module Main ( main ) where

import qualified Data.Map as M
import Data.Monoid
import qualified Data.Set as S
import System.FilePath ( (<.>) )
import System.Environment ( getArgs, withArgs )
import Test.HUnit ( assertEqual )

import LLVM.Analysis
import LLVM.Analysis.CallGraph
import LLVM.Analysis.CallGraphSCCTraversal
import LLVM.Analysis.PointsTo
import LLVM.Analysis.PointsTo.TrivialFunction
import LLVM.Analysis.Util.Testing
import LLVM.Parse

import Foreign.Inference.Interface
import Foreign.Inference.Preprocessing
import Foreign.Inference.Analysis.Finalize
import Foreign.Inference.Analysis.RefCount
import Foreign.Inference.Analysis.ScalarEffects
import Foreign.Inference.Analysis.SingleInitializer
import Foreign.Inference.Analysis.Util.CompositeSummary

main :: IO ()
main = do
  args <- getArgs
  let pattern = case args of
        [] -> "tests/ref-counting/*.c"
        [infile] -> infile
  ds <- loadDependencies [] []
  let testDescriptors = [ TestDescriptor { testPattern = pattern
                                         , testExpectedMapping = (<.> "expected")
                                         , testResultBuilder = analyzeRefCounts ds
                                         , testResultComparator = assertEqual
                                         }
                        ]
  withArgs [] $ testAgainstExpected requiredOptimizations parser testDescriptors
  where
    parser = parseLLVMFile defaultParserOptions

analyzeRefCounts ds m =
  refCountSummaryToTestFormat (_refCountSummary res)
  where
    sis = identifySingleInitializers m
    pta = runPointsToAnalysis m
    cg = mkCallGraph m pta []
    analyses :: [ComposableAnalysis AnalysisSummary FunctionMetadata]
    analyses = [ identifyFinalizers ds sis finalizerSummary
               , identifyScalarEffects scalarEffectSummary
               , identifyRefCounting ds refCountSummary finalizerSummary scalarEffectSummary
               ]
    analysisFunc = callGraphComposeAnalysis analyses
    res = callGraphSCCTraversal cg analysisFunc mempty
