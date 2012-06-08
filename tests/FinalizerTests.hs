module Main ( main ) where

import Data.Map ( Map )
import Data.Monoid
import Data.Set ( Set )
import System.FilePath ( (<.>) )
import System.Environment ( getArgs, withArgs )
import Test.HUnit ( assertEqual )

import LLVM.Analysis
import LLVM.Analysis.CallGraph
import LLVM.Analysis.CallGraphSCCTraversal
import LLVM.Analysis.Util.Testing
import LLVM.Parse

import Foreign.Inference.Interface
import Foreign.Inference.Preprocessing
import Foreign.Inference.Analysis.Finalize
import Foreign.Inference.Analysis.IndirectCallResolver
import Foreign.Inference.Analysis.Util.CompositeSummary

main :: IO ()
main = do
  args <- getArgs
  let pattern = case args of
        [] -> "tests/finalize/*.c"
        [infile] -> infile
        _ -> error "At most one argument allowed"
  ds <- loadDependencies ["tests/finalize"] []
  let testDescriptors = [ TestDescriptor { testPattern = pattern
                                         , testExpectedMapping = (<.> "expected")
                                         , testResultBuilder = analyzeFinalize ds
                                         , testResultComparator = assertEqual
                                         }
                        ]
  withArgs [] $ testAgainstExpected requiredOptimizations parser testDescriptors
  where
    parser = parseLLVMFile defaultParserOptions

analyzeFinalize :: DependencySummary -> Module -> Map String (Set String)
analyzeFinalize ds m =
  finalizerSummaryToTestFormat (_finalizerSummary res)
  where
    ics = identifyIndirectCallTargets m
    cg = mkCallGraph m ics []
    analyses :: [ComposableAnalysis AnalysisSummary FunctionMetadata]
    analyses = [ identifyFinalizers ds ics finalizerSummary ]
    analysisFunc = callGraphComposeAnalysis analyses
    res = callGraphSCCTraversal cg analysisFunc mempty
