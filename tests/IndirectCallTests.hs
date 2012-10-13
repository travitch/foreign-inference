module Main ( main ) where

import qualified Data.Foldable as F
import Data.Monoid
import Data.Set ( Set )
import qualified Data.Set as S
import System.FilePath ( (<.>) )
import System.Environment ( getArgs, withArgs )
import Test.HUnit ( assertEqual )

import LLVM.Analysis
import LLVM.Analysis.Util.Testing
import LLVM.Parse

import Foreign.Inference.Preprocessing
import Foreign.Inference.Analysis.IndirectCallResolver

main :: IO ()
main = do
  args <- getArgs
  let pattern = case args of
        [] -> "tests/indirect-calls/*.c"
        [infile] -> infile
        _ -> error "At most one argument allowed"
  let testDescriptors = [ TestDescriptor { testPattern = pattern
                                         , testExpectedMapping = (<.> "expected")
                                         , testResultBuilder = checkIndirectTargets
                                         , testResultComparator = assertEqual
                                         }
                        ]
  withArgs [] $ testAgainstExpected requiredOptimizations parser testDescriptors
  where
    parser = parseLLVMFile defaultParserOptions

-- | Find the first indirect call in the Module and return the set of
-- functions it could possibly point to.
checkIndirectTargets :: Module -> Set String
checkIndirectTargets m =
  foldr targetNames mempty (indirectCallInitializers ics callee)
  where
    fs = moduleDefinedFunctions m
    Just i = F.find isIndirectCallInst (concatMap functionInstructions fs)
    callee = callFunction i
    ics = identifyIndirectCallTargets m

isIndirectCallInst :: Instruction -> Bool
isIndirectCallInst i =
  case i of
    CallInst { callFunction = cf } ->
      case valueContent' cf of
        FunctionC _ -> False
        ExternalFunctionC _ -> False
        _ -> True
    _ -> False

targetNames :: Value -> Set String -> Set String
targetNames v = S.insert (identifierAsString n)
  where
    Just n = valueName (stripBitcasts v)
