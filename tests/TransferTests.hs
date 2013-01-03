module Main ( main ) where

import Data.Map ( Map )
import Data.Monoid
import Data.Set ( Set )
import System.Environment ( getArgs, withArgs )
import System.FilePath ( (<.>) )
import Test.HUnit ( assertEqual )

import LLVM.Analysis
import LLVM.Analysis.CallGraph
import LLVM.Analysis.CallGraphSCCTraversal
import LLVM.Analysis.Util.Testing
import LLVM.Parse

import Foreign.Inference.Interface
import Foreign.Inference.Preprocessing
import Foreign.Inference.Analysis.Finalize
import Foreign.Inference.Analysis.Transfer
import Foreign.Inference.Analysis.IndirectCallResolver
import Foreign.Inference.Analysis.Util.CompositeSummary

main :: IO ()
main = do
  args <- getArgs
  let pattern = case args of
        [] -> "tests/transfer/*.c"
        [infile] -> infile
        _ -> error "Only zero or one arguments allowed"
  ds <- loadDependencies ["tests/transfer"] []
  let testDescriptors = [ TestDescriptor { testPattern = pattern
                                         , testExpectedMapping = (<.> "expected")
                                         , testResultBuilder = analyzeTransfer ds
                                         , testResultComparator = assertEqual
                                         }
                        ]
  withArgs [] $ testAgainstExpected requiredOptimizations bcParser testDescriptors
  where
    bcParser = parseLLVMFile defaultParserOptions

analyzeTransfer :: DependencySummary -> Module -> Map String (Set String)
analyzeTransfer ds m =
  transferSummaryToTestFormat (_transferSummary res)
  where
    pta = identifyIndirectCallTargets m
    cg = mkCallGraph m pta []
    funcLikes :: [FunctionMetadata]
    funcLikes = map fromFunction (moduleDefinedFunctions m)
    analyses :: [ComposableAnalysis AnalysisSummary FunctionMetadata]
    analyses = [ identifyFinalizers ds pta finalizerSummary ]
    pfunc = callGraphComposeAnalysis analyses
    res0 = parallelCallGraphSCCTraversal cg pfunc mempty
    res = identifyTransfers funcLikes ds pta res0 finalizerSummary transferSummary
