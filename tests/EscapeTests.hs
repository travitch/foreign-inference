module Main ( main ) where

import Data.Map ( Map )
import Data.Monoid
import Data.Set ( Set )
import System.Environment ( getArgs, withArgs )
import System.FilePath
import Test.HUnit ( assertEqual )

import LLVM.Analysis
import LLVM.Analysis.CallGraph
import LLVM.Analysis.CallGraphSCCTraversal
import LLVM.Analysis.Util.Testing
import LLVM.Parse

import Foreign.Inference.Interface
import Foreign.Inference.Preprocessing
import Foreign.Inference.Analysis.Escape
import Foreign.Inference.Analysis.IndirectCallResolver
import Foreign.Inference.Analysis.Util.CompositeSummary

main :: IO ()
main = do
  args <- getArgs
  let pattern = case args of
        [] -> "tests/escape/proper-escapes/*.c"
        [infile] -> infile
        _ -> error "At most one argument allowed"
  ds <- loadDependencies [] []
  let testDescriptors = [
        TestDescriptor { testPattern = pattern
                       , testExpectedMapping = (<.> "expected")
                       , testResultBuilder = analyzeEscapes ds
                       , testResultComparator = assertEqual
                       }
        ]
  withArgs [] $ testAgainstExpected requiredOptimizations bcParser testDescriptors
  where
    bcParser = parseLLVMFile defaultParserOptions



analyzeEscapes :: DependencySummary -> Module -> Map String (Set (EscapeClass, String))
analyzeEscapes ds m =
  escapeResultToTestFormat (_escapeSummary res)
  where
    ics = identifyIndirectCallTargets m
    cg = mkCallGraph m ics []
    analyses :: [ComposableAnalysis AnalysisSummary FunctionMetadata]
    analyses = [ identifyEscapes ds ics escapeSummary ]
    analysisFunc = callGraphComposeAnalysis analyses
    res = callGraphSCCTraversal cg analysisFunc mempty



-- runEscapeAnalysis ::  CallGraph
--                      -> (ExternalFunction -> Int -> Identity Bool)
--                      -> EscapeSummary
-- runEscapeAnalysis cg extSumm =
--   let analyses = [ identifyEscapes extSumm
--         callGraphAnalysisM runIdentity (identifyEscapes extSumm)
--   in callGraphSCCTraversal cg analysis mempty

-- These tests assume that any external function allows all of its
-- arguments to escape.
-- properEscapeSummary :: Module -> Map String (Set String)
-- properEscapeSummary m = escapeResultToTestFormat er
--   where
--     pta = runPointsToAnalysis m
--     cg = mkCallGraph m pta []
--     er = runEscapeAnalysis cg externalFuncSummary


-- -- | This external function summary lets us call puts and printf and
-- -- marks the argument as not escaping
-- externalFuncSummary :: ExternalFunction -> Int -> Identity Bool
-- externalFuncSummary ef _ =
--   case identifierAsString (externalFunctionName ef) `elem` ["puts", "printf"] of
--     True -> return False
--     False -> return True

-- willEscapeSummary :: Module -> Map String (Set String)
-- willEscapeSummary m = willEscapeResultToTestFormat er
--   where
--     pta = runPointsToAnalysis m
--     cg = mkCallGraph m pta []
--     er = runEscapeAnalysis cg extSumm
--     extSumm _ _ = return True
