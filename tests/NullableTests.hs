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
import LLVM.Analysis.Util.Testing
import LLVM.Parse

import Foreign.Inference.Interface
import Foreign.Inference.Preprocessing
import Foreign.Inference.Analysis.IndirectCallResolver
import Foreign.Inference.Analysis.Nullable
import Foreign.Inference.Analysis.Return
import Foreign.Inference.Analysis.Util.CompositeSummary

main :: IO ()
main = do
  args <- getArgs
  let pattern = case args of
        [] -> "tests/nullable/*.c"
        [infile] -> infile
  ds <- loadDependencies ["tests/nullable"] ["base"]
  let testDescriptors = [ TestDescriptor { testPattern = pattern
                                         , testExpectedMapping = (<.> "expected")
                                         , testResultBuilder = analyzeNullable ds
                                         , testResultComparator = assertEqual
                                         }
                        ]
  withArgs [] $ testAgainstExpected requiredOptimizations parser testDescriptors
  where
    parser = parseLLVMFile defaultParserOptions

analyzeNullable ds m =
  nullSummaryToTestFormat (_nullableSummary res)
  where
    pta = identifyIndirectCallTargets m
    cg = mkCallGraph m pta []
    analyses :: [ComposableAnalysis AnalysisSummary FunctionMetadata]
    analyses = [ identifyReturns ds returnSummary
               , identifyNullable ds nullableSummary returnSummary
               ]
    analysisFunc = callGraphComposeAnalysis analyses
    res = callGraphSCCTraversal cg analysisFunc mempty
