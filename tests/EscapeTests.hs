module Main ( main ) where

import Data.List ( find )
import Data.Map ( Map )
import Data.Maybe ( isJust )
import Data.Monoid
import Data.Set ( Set )
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
  ds <- loadDependencies [] []
  let testDescriptors = [
        TestDescriptor { testPattern = "tests/escape/proper-escapes/*.c"
                       , testExpectedMapping = (<.> "expected")
                       , testResultBuilder = analyzeEscapes ds
                       , testResultComparator = assertEqual
                       }
        -- , TestDescriptor { testPattern = "tests/escape/will-escape/*.c"
        --                  , testExpectedMapping = (<.> "expected")
        --                  , testResultBuilder = willEscapeSummary
        --                  , testResultComparator = assertEqual
        --                  }

        , TestDescriptor { testPattern = "tests/escape/instruction-escape/*.c"
                         , testExpectedMapping = (<.> "expected")
                         , testResultBuilder = analyzeInstructionEscapes ds
                         , testResultComparator = assertEqual
                         }
        ]

  testAgainstExpected requiredOptimizations bcParser testDescriptors
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


analyzeInstructionEscapes :: DependencySummary -> Module -> Bool
analyzeInstructionEscapes ds m =
  isJust $ instructionEscapesWith notReturn i (_escapeSummary res)
  where
    ics = identifyIndirectCallTargets m
    cg = mkCallGraph m ics []
    analyses :: [ComposableAnalysis AnalysisSummary FunctionMetadata]
    analyses = [ identifyEscapes ds ics escapeSummary ]
    analysisFunc = callGraphComposeAnalysis analyses
    res = callGraphSCCTraversal cg analysisFunc mempty
    Just i = find isCallInst (moduleInstructions m)
    notReturn ignoreInst =
      case ignoreInst of
        RetInst {} -> True
        _ -> False


moduleInstructions :: Module -> [Instruction]
moduleInstructions = concatMap functionInstructions . moduleDefinedFunctions


isCallInst :: Instruction -> Bool
isCallInst i =
  case i of
    CallInst {} -> True
    _ -> False

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
