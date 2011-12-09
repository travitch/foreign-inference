module Main ( main ) where

import qualified Data.Map as M
import qualified Data.Set as S
import System.FilePath ( (<.>) )
import System.Environment ( getArgs, withArgs )
import Test.HUnit ( assertEqual )

import Data.LLVM
import Data.LLVM.CallGraph
import Data.LLVM.Analysis.Escape
import Data.LLVM.Analysis.PointsTo
import Data.LLVM.Analysis.PointsTo.TrivialFunction
import Data.LLVM.Parse
import Data.LLVM.Testing

import Foreign.Inference.Interface
import Foreign.Inference.Analysis.Nullable

main :: IO ()
main = do
  args <- getArgs
  let pattern = case args of
        [] -> "tests/nullable/*.c"
        [infile] -> infile
  ds <- loadDependencies' [] "tests/nullable" ["base"]
  let testDescriptors = [ TestDescriptor { testPattern = pattern
                                         , testExpectedMapping = (<.> "expected")
                                         , testResultBuilder = analyzeNullable ds
                                         , testResultComparator = assertEqual
                                         }
                        ]
  withArgs [] $ testAgainstExpected parser testDescriptors
  where
    parser = parseLLVMFile defaultParserOptions

analyzeNullable ds m = nullSummaryToTestFormat $ identifyNullable ds m cg er
  where
    pta = runPointsToAnalysis m
    cg = mkCallGraph m pta []
    er = runEscapeAnalysis m cg
{-
convertSummary = M.mapKeys keyMapper . M.map valMapper . M.filter notEmptySet
  where
    notEmptySet = not . S.null
    valMapper = S.map (show . argumentName)
    keyMapper = show . functionName
-}