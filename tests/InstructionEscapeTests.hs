module Main ( main ) where

import Data.List ( find )
import Data.Maybe ( isJust )
import Data.Monoid
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
        [] -> "tests/escape/instruction-escape/*.c"
        [infile] -> infile
        _ -> error "At most one argument allowed"
  ds <- loadDependencies [] []
  let testDescriptors = [
        TestDescriptor { testPattern = pattern
                       , testExpectedMapping = (<.> "expected")
                       , testResultBuilder = analyzeInstructionEscapes ds
                       , testResultComparator = assertEqual
                       }
        ]

  withArgs [] $ testAgainstExpected requiredOptimizations bcParser testDescriptors
  where
    bcParser = parseLLVMFile defaultParserOptions

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
