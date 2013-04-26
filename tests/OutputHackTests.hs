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
import Foreign.Inference.Analysis.Allocator
import Foreign.Inference.Analysis.Escape
import Foreign.Inference.Analysis.Finalize
import Foreign.Inference.Analysis.Output
import Foreign.Inference.Analysis.IndirectCallResolver
import Foreign.Inference.Analysis.Util.CompositeSummary

main :: IO ()
main = do
  args <- getArgs
  let pattern = case args of
        [] -> "tests/output-hack/*.c"
        [infile] -> infile
        _ -> error "At most one argument allowed"
  ds <- loadDependencies [] []
  let testDescriptors = [ TestDescriptor { testPattern = pattern
                                         , testExpectedMapping = (<.> "expected")
                                         , testResultBuilder = analyzeOutput ds
                                         , testResultComparator = assertEqual
                                         }
                        ]
  withArgs [] $ testAgainstExpected requiredOptimizations parser testDescriptors
  where
    parser = parseLLVMFile defaultParserOptions

analyzeOutput :: DependencySummary -> Module -> Map String (Set (String, ParamAnnotation))
analyzeOutput ds m =
  outputSummaryToTestFormat (_outputSummary res)
  where
    outCfg = defaultOutAnalysisConfig { trivialBlockHack = True }
    cg = callGraph m ics []
    ics = identifyIndirectCallTargets m
    analyses :: [ComposableAnalysis AnalysisSummary FunctionMetadata]
    analyses = [ identifyEscapes ds ics escapeSummary
               , identifyFinalizers ds ics finalizerSummary
               , identifyAllocators ds ics allocatorSummary escapeSummary finalizerSummary
               , identifyOutput outCfg ds outputSummary allocatorSummary escapeSummary
               ]
    analysisFunc = callGraphComposeAnalysis analyses
    res = callGraphSCCTraversal cg analysisFunc mempty
