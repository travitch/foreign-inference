import Data.Map ( Map )
import qualified Data.Map as M
import Data.Maybe ( fromJust )
import Data.Set ( Set )
import qualified Data.Set as S
import qualified Data.HashSet as HS

import Test.HUnit

import Data.LLVM
import Data.LLVM.CFG
import Data.LLVM.Types
import Data.LLVM.Analysis.Dataflow
import Data.LLVM.Testing

import Foreign.Inference.Nullability

type StringSet = Set String
notNullParameterTest :: Module -> Map String StringSet
notNullParameterTest m = M.fromList exitRes''
  where
    fs = moduleDefinedFunctions m
    cfgs = map mkCFG fs
    names = map (show . fromJust . valueName) fs
    na0 = emptyNullabilityAnalysis
    res = map (forwardDataflow na0) cfgs
    -- get the results at the exit node for each function by applying
    -- the 'res' function to the exit value for each function.
    exitRes = map (\(x,y) -> x y) (zip res (map cfgExitValue cfgs))
    exitRes' = map (S.map (show . fromJust . valueName) . S.filter isArgument . S.fromList . HS.toList) (map notNullablePtrs exitRes)
    exitRes'' = zip names exitRes'

isArgument :: Value -> Bool
isArgument Value { valueContent = Argument _ } = True
isArgument _ = False

expectedMapper :: FilePath -> FilePath
expectedMapper = (++ ".expected")

main :: IO ()
main = do
  let pattern = "tests/nullability/params/*.c"
  testAgainstExpected pattern expectedMapper True notNullParameterTest assertEqual