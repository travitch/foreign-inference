module Main ( main ) where

import System.FilePath ( (<.>) )
import System.Environment ( getArgs, withArgs )
import Test.HUnit ( assertEqual )

import Data.LLVM
import Data.LLVM.Analysis.CallGraph
import Data.LLVM.Analysis.PointsTo.TrivialFunction
import Data.LLVM.Parse
import Data.LLVM.Testing

import Foreign.Inference.Interface
import Foreign.Inference.Preprocessing
import Foreign.Inference.Analysis.Allocator
import Foreign.Inference.Analysis.Escape

main :: IO ()
main = do
  args <- getArgs
  let pattern = case args of
        [] -> "tests/allocator/*.c"
        [infile] -> infile
  ds <- loadDependencies' [] [] ["c"]
  let testDescriptors = [ TestDescriptor { testPattern = pattern
                                         , testExpectedMapping = (<.> "expected")
                                         , testResultBuilder = analyzeAllocator ds
                                         , testResultComparator = assertEqual
                                         }
                        ]
  withArgs [] $ testAgainstExpected requiredOptimizations parser testDescriptors
  where
    parser = parseLLVMFile defaultParserOptions

analyzeAllocator ds m = allocatorSummaryToTestFormat ar
  where
    pta = runPointsToAnalysis m
    cg = mkCallGraph m pta []
    (er, _) = identifyEscapes ds cg
    (ar, _) = identifyAllocators ds er cg