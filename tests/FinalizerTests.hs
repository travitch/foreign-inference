module Main ( main ) where

import System.FilePath ( (<.>) )
import System.Environment ( getArgs, withArgs )
import Test.HUnit ( assertEqual )

import Data.LLVM
import Data.LLVM.Analysis.CallGraph
import Data.LLVM.Analysis.PointsTo
import Data.LLVM.Analysis.PointsTo.TrivialFunction
import Data.LLVM.Parse
import Data.LLVM.Testing

import Foreign.Inference.Interface
import Foreign.Inference.Preprocessing
import Foreign.Inference.Analysis.Finalize

main :: IO ()
main = do
  args <- getArgs
  let pattern = case args of
        [] -> "tests/finalize/*.c"
        [infile] -> infile
  ds <- loadDependencies' [] ["tests/finalize"] ["c"]
  let testDescriptors = [ TestDescriptor { testPattern = pattern
                                         , testExpectedMapping = (<.> "expected")
                                         , testResultBuilder = analyzeFinalize ds
                                         , testResultComparator = assertEqual
                                         }
                        ]
  withArgs [] $ testAgainstExpected requiredOptimizations parser testDescriptors
  where
    parser = parseLLVMFile defaultParserOptions

analyzeFinalize ds m = finalizerSummaryToTestFormat $ fst $ identifyFinalizers ds cg
  where
    pta = runPointsToAnalysis m
    cg = mkCallGraph m pta []
