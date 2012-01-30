module Main ( main ) where

import System.Environment ( getArgs, withArgs )
import System.FilePath ( (<.>) )
import Test.HUnit ( assertEqual )

import Data.LLVM
import Data.LLVM.Parse
import Data.LLVM.Analysis.CallGraph
import Data.LLVM.Analysis.PointsTo
import Data.LLVM.Analysis.PointsTo.TrivialFunction
import Data.LLVM.Testing

import Foreign.Inference.Interface
import Foreign.Inference.Preprocessing
import Foreign.Inference.Analysis.Array

import Debug.Trace
debug = flip trace

main :: IO ()
main = do
  args <- getArgs
  let pattern = case args of
        [] -> "tests/arrays/*.c"
        [infile] -> infile
  ds <- loadDependencies' [] ["tests/arrays"] ["base"]
  let testDescriptors = [ TestDescriptor { testPattern = pattern
                                         , testExpectedMapping = (<.> "expected")
                                         , testResultBuilder = analyzeArrays ds
                                         , testResultComparator = assertEqual
                                         }
                        ]
  withArgs [] $ testAgainstExpected requiredOptimizations bcParser testDescriptors
  where
    bcParser = parseLLVMFile defaultParserOptions

analyzeArrays ds m = arraySummaryToTestFormat $ fst $ identifyArrays ds cg
  where
    pta = runPointsToAnalysis m
    cg = mkCallGraph m pta []
