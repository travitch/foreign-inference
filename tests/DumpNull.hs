module Main ( main ) where

import System.Environment ( getArgs )

import Data.LLVM.CallGraph
import Data.LLVM.Analysis.Escape
import Data.LLVM.Analysis.PointsTo.TrivialFunction
import Data.LLVM.Parse
import Foreign.Inference.Interface
import Foreign.Inference.Analysis.Nullable

main :: IO ()
main = do
  [inFile, name] <- getArgs
  Right m <- parseLLVMFile defaultParserOptions inFile
  let pta = runPointsToAnalysis m
      cg = mkCallGraph m pta []
      er = runEscapeAnalysis m cg
  ds <- loadDependencies' [] "." []
  let s = identifyNullable ds m cg er
  saveModule "." name [] m [s]