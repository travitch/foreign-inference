module Main ( main ) where

import Data.Map ( Map )
import Data.Monoid
import Data.Set ( Set )
import System.Environment ( getArgs, withArgs )
import System.FilePath
import Test.HUnit ( assertEqual )

import LLVM.Analysis
import LLVM.Analysis.AccessPath
import LLVM.Analysis.CallGraph
import LLVM.Analysis.CallGraphSCCTraversal
import LLVM.Analysis.Util.Testing
import LLVM.Parse

import Foreign.Inference.Interface
import Foreign.Inference.Preprocessing
import Foreign.Inference.Analysis.IndirectCallResolver
import Foreign.Inference.Analysis.SAP
import Foreign.Inference.Analysis.Util.CompositeSummary

main :: IO ()
main = do
  args <- getArgs
  let pattern = case args of
        [] -> "tests/sap/argument/*.c"
        [infile] -> infile
        _ -> error "At most one argument allowed"
  ds <- loadDependencies [] []
  let testDescriptors = [
        TestDescriptor { testPattern = pattern
                       , testExpectedMapping = (<.> "expected")
                       , testResultBuilder = analyzeSAPs ds
                       , testResultComparator = assertEqual
                       }
        ]
  withArgs [] $ testAgainstExpected requiredOptimizations bcParser testDescriptors
  where
    bcParser = parseLLVMFile defaultParserOptions

type Summary = (Int, String, [AccessType])

analyzeSAPs :: DependencySummary -> Module -> Map (String, String) (Set Summary)
analyzeSAPs ds m =
  sapArgumentResultToTestFormat (_sapSummary res)
  where
    ics = identifyIndirectCallTargets m
    cg = mkCallGraph m ics []
    analyses :: [ComposableAnalysis AnalysisSummary FunctionMetadata]
    analyses = [ identifySAPs ds sapSummary ]
    analysisFunc = callGraphComposeAnalysis analyses
    res = callGraphSCCTraversal cg analysisFunc mempty
