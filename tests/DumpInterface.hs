module Main ( main ) where

import Control.Exception ( tryJust )
import Control.Monad ( guard, when )
import Data.Monoid
import System.Console.CmdArgs.Explicit
import System.Console.CmdArgs.Text
import System.Environment ( getEnv )
import System.Exit
import System.FilePath
import System.IO.Error ( isDoesNotExistError )

import Data.LLVM.CallGraph
import Data.LLVM.Analysis.Escape
import Data.LLVM.Analysis.PointsTo.TrivialFunction
import Data.LLVM.Parse

import Foreign.Inference.Diagnostics
import Foreign.Inference.Interface
import Foreign.Inference.Analysis.Array
import Foreign.Inference.Analysis.Nullable

cmdOpts :: Opts -> Mode Opts
cmdOpts defs = mode "DumpInterface" defs desc bitcodeArg as
  where
    bitcodeArg = (flagArg setBitcode "BITCODE")
    desc = "A frontend for the FFI Inference engine"
    as = [ flagReq ["dependency", "dep"] addDependency "DEPENDENCY" "A dependency of the library being analyzed."
         , flagReq ["repository"] setRepository "REPOSITORY" "The directory containing dependency summaries.  The summary of the input library will be stored here. (Default: consult environment)"
         , flagReq ["diagnostics"] setDiagnostics "DIAGNOSTIC" "The level of diagnostics to show (Debug, Info, Warning, Error).  Default: Warning"
         , flagHelpSimple setHelp
         ]

-- | The repository location is first chosen based on an environment
-- variable.  The command line argument, if specified, will override
-- it.  If the environment variable is not set, the command line
-- argument must be specified.
data Opts = Opts { inputDependencies :: [String]
                 , repositoryLocation :: FilePath
                 , inputFile :: [FilePath]
                 , diagnosticLevel :: Classification
                 , wantsHelp :: Bool
                 }
          deriving (Show)

defOpts :: FilePath -> Opts
defOpts rl = Opts { inputDependencies = []
                  , repositoryLocation = rl
                  , inputFile = []
                  , diagnosticLevel = Info
                  , wantsHelp = False
                  }

addDependency :: String -> Opts -> Either String Opts
addDependency dep opts =
  Right opts { inputDependencies = dep : inputDependencies opts }

setBitcode :: String -> Opts -> Either String Opts
setBitcode inf opts@Opts { inputFile = [] } = Right opts { inputFile = [inf] }
setBitcode _ _ = Left "Only one input library is allowed"

setRepository :: String -> Opts -> Either String Opts
setRepository r opts = Right opts { repositoryLocation = r }

setDiagnostics :: String -> Opts -> Either String Opts
setDiagnostics d opts =
  case reads d of
    [] -> Left $ "Invalid diagnostic level: " ++ d
    [(diagLevel, "")] -> Right opts { diagnosticLevel = diagLevel }
    _ -> Left $ "Invalid diagnostic level: " ++ d

setHelp :: Opts -> Opts
setHelp opts = opts { wantsHelp = True }

showHelpAndExit :: Mode a -> IO b -> IO b
showHelpAndExit arguments exitCmd = do
  putStrLn $ showText (Wrap 80) $ helpText [] HelpFormatOne arguments
  exitCmd

main :: IO ()
main = do
  mRepLoc <- tryJust (guard . isDoesNotExistError) (getEnv "INFERENCE_REPOSITORY")
  let repLoc = either (error "No dependency repository specified") id mRepLoc
      defs = defOpts repLoc
      arguments = cmdOpts defs
  opts <- processArgs arguments

  when (wantsHelp opts) (showHelpAndExit arguments exitSuccess)
  when (length (inputFile opts) /= 1) (showHelpAndExit arguments exitFailure)

  let [inFile] = inputFile opts
      deps = inputDependencies opts
      repo = repositoryLocation opts
      name = takeBaseName inFile
  Right m <- parseLLVMFile defaultParserOptions inFile

  let pta = runPointsToAnalysis m
      cg = mkCallGraph m pta []
      er = runEscapeAnalysis m cg
  ds <- loadDependencies [repo] deps

  let (s, nullDiags) = identifyNullable ds m cg er
      (a, arrayDiags) = identifyArrays ds cg er
      diags = mconcat [ nullDiags, arrayDiags ]
  case formatDiagnostics (diagnosticLevel opts) diags of
    Nothing -> return ()
    Just diagString -> putStrLn diagString
  saveModule repo name deps m [ModuleSummary s, ModuleSummary a]
