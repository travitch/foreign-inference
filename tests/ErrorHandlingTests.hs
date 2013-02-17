module Main ( main ) where

import qualified Data.Foldable as F
import Data.Map ( Map )
import qualified Data.Map as M
import Data.Maybe ( fromMaybe, mapMaybe )
import Data.Monoid
import Data.Set ( Set )
import qualified Data.Set as S
import System.Environment ( getArgs, withArgs )
import System.FilePath ( (<.>) )
import Test.HUnit ( assertEqual )

import LLVM.Analysis
import LLVM.Analysis.Util.Testing
import LLVM.Parse

import Foreign.Inference.Interface
import Foreign.Inference.Preprocessing
import Foreign.Inference.Analysis.ErrorHandling
import Foreign.Inference.Analysis.IndirectCallResolver
import Foreign.Inference.Analysis.Util.CompositeSummary

main :: IO ()
main = do
  args <- getArgs
  let pattern = case args of
        [] -> "tests/error-handling/*.c"
        [infile] -> infile
  ds <- loadDependencies ["tests/error-handling"] []
  let testDescriptors = [ TestDescriptor { testPattern = pattern
                                         , testExpectedMapping = (<.> "expected")
                                         , testResultBuilder = analyzeErrors ds
                                         , testResultComparator = assertEqual
                                         }
                        ]
  withArgs [] $ testAgainstExpected requiredOptimizations bcParser testDescriptors
  where
    bcParser = parseLLVMFile defaultParserOptions

type TestFormat = Map String (Set String, ErrorReturn)

analyzeErrors :: DependencySummary -> Module -> TestFormat
analyzeErrors ds m = toTestFormat eres fs
  where
    pta = identifyIndirectCallTargets m
    fs = moduleDefinedFunctions m
    funcLikes :: [FunctionMetadata]
    funcLikes = map fromFunction (moduleDefinedFunctions m)
    eres = identifyErrorHandling funcLikes ds pta

toTestFormat :: ErrorSummary -> [Function] -> TestFormat
toTestFormat eres = foldr checkSummary mempty
  where
    checkSummary f acc = fromMaybe acc $ do
      let s = summarizeFunction f eres
      (FAReportsErrors acts rcs, _) <- F.find isErrRetAnnot s
      let fname = identifierAsString (functionName f)
      return $ M.insert fname (errorFuncs acts, rcs) acc

isErrRetAnnot :: (FuncAnnotation, a) -> Bool
isErrRetAnnot (a, _) =
  case a of
    FAReportsErrors _ _ -> True
    _ -> False

errorFuncs :: Set ErrorAction -> Set String
errorFuncs = S.fromList . mapMaybe toErrFunc . S.toList
  where
    toErrFunc a =
      case a of
        FunctionCall fname _ -> return fname
        _ -> Nothing