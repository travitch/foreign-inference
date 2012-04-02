module Main ( main ) where

import Control.Exception ( tryJust )
import Data.Lens.Common
import Data.Monoid
import System.Console.CmdArgs.Explicit
import System.Console.CmdArgs.Text
import System.Environment ( getEnv )
import System.Exit
import System.FilePath
import System.IO.Error ( isDoesNotExistError )

import Codec.Archive

import LLVM.Analysis
import LLVM.Analysis.CallGraph
import LLVM.Analysis.CallGraphSCCTraversal
import LLVM.Analysis.PointsTo.TrivialFunction
import LLVM.Parse

import Foreign.Inference.Diagnostics
import Foreign.Inference.Interface
import Foreign.Inference.Report
import Foreign.Inference.Preprocessing
import Foreign.Inference.AnalysisMonad
import Foreign.Inference.Analysis.Allocator
import Foreign.Inference.Analysis.Array
import Foreign.Inference.Analysis.Escape
import Foreign.Inference.Analysis.Finalize
import Foreign.Inference.Analysis.Nullable
import Foreign.Inference.Analysis.Output
import Foreign.Inference.Analysis.RefCount
import Foreign.Inference.Analysis.Return
import Foreign.Inference.Analysis.ScalarEffects
import Foreign.Inference.Analysis.SingleInitializer
import Foreign.Inference.Analysis.Util.CompositeSummary

-- Command line helpers
addDependency :: String -> Opts -> Either String Opts
addDependency dep opts =
  Right opts { inputDependencies = dep : inputDependencies opts }

setBitcode :: String -> Opts -> Either String Opts
setBitcode inf opts@Opts { inputFile = [] } = Right opts { inputFile = [inf] }
setBitcode _ _ = Left "Only one input library is allowed"

setRepository :: String -> Opts -> Either String Opts
setRepository r opts = Right opts { repositoryLocation = r }

setSource :: String -> Opts -> Either String Opts
setSource s opts = Right opts { librarySource = Just s }

setReportDir :: String -> Opts -> Either String Opts
setReportDir d opts = Right opts { reportDir = Just d }

setDiagnostics :: String -> Opts -> Either String Opts
setDiagnostics d opts =
  case reads d of
    [] -> Left $ "Invalid diagnostic level: " ++ d
    [(diagLevel, "")] -> Right opts { diagnosticLevel = diagLevel }
    _ -> Left $ "Invalid diagnostic level: " ++ d

setAnnotations :: String -> Opts -> Either String Opts
setAnnotations a opts = Right opts { annotationFile = Just a }

setHelp :: Opts -> Opts
setHelp opts = opts { wantsHelp = True }

cmdOpts :: Opts -> Mode Opts
cmdOpts defs = mode "IIGlue" defs desc bitcodeArg as
  where
    bitcodeArg = (flagArg setBitcode "BITCODE")
    desc = "A frontend for the FFI Inference engine"
    as = [ flagReq ["dependency"] addDependency "DEPENDENCY" "A dependency of the library being analyzed."
         , flagReq ["repository"] setRepository "DIRECTORY" "The directory containing dependency summaries.  The summary of the input library will be stored here. (Default: consult environment)"
         , flagReq ["diagnostics"] setDiagnostics "DIAGNOSTIC" "The level of diagnostics to show (Debug, Info, Warning, Error).  Default: Warning"
         , flagReq ["source"] setSource "FILE" "The source for the library being analyzed (tarball or zip archive).  If provided, a report will be generated"
         , flagReq ["reportDir"] setReportDir "DIRECTORY" "The directory in which the summary report will be produced.  Defaults to the REPOSITORY."
         , flagReq ["annotations"] setAnnotations "FILE" "An optional file containing annotations for the library being analyzed"
         , flagHelpSimple setHelp
         ]

-- | The repository location is first chosen based on an environment
-- variable.  The command line argument, if specified, will override
-- it.  If the environment variable is not set, the command line
-- argument must be specified.
data Opts = Opts { inputDependencies :: [String]
                 , repositoryLocation :: FilePath
                 , librarySource :: Maybe FilePath
                 , reportDir :: Maybe FilePath
                 , inputFile :: [FilePath]
                 , diagnosticLevel :: Classification
                 , annotationFile :: Maybe FilePath
                 , wantsHelp :: Bool
                 }
          deriving (Show)

defOpts :: FilePath -> Opts
defOpts rl = Opts { inputDependencies = []
                  , repositoryLocation = rl
                  , librarySource = Nothing
                  , reportDir = Nothing
                  , inputFile = []
                  , diagnosticLevel = Info
                  , annotationFile = Nothing
                  , wantsHelp = False
                  }


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
      name = takeBaseName inFile
      parseOpts = case librarySource opts of
        Nothing -> defaultParserOptions { metaPositionPrecision = PositionNone }
        Just _ -> defaultParserOptions
  mm <- readBitcode (parseLLVMFile parseOpts) inFile
  either error (dump opts name) mm

dump :: Opts -> String -> Module -> IO ()
dump opts name m = do
  let pta = runPointsToAnalysis m
      cg = mkCallGraph m pta []
      deps = inputDependencies opts
      repo = repositoryLocation opts
  baseDeps <- loadDependencies [repo] deps
  ds <- case annotationFile opts of
    Nothing -> return baseDeps
    Just af -> do
      annots <- loadAnnotations af
      return $! addLibraryAnnotations baseDeps annots

  let sis = identifySingleInitializers m

  -- Have to give a type signature here to fix all of the FuncLike
  -- constraints to our metadata blob.
  let analyses :: [ComposableAnalysis AnalysisSummary FunctionMetadata]
      analyses = [ identifyReturns ds returnSummary
                 , identifyScalarEffects scalarEffectSummary
                 , identifyArrays ds arraySummary
                 , identifyFinalizers ds sis finalizerSummary
                 , identifyEscapes ds escapeSummary
                 , identifyOutput ds outputSummary
                 , identifyNullable ds nullableSummary returnSummary
                 , identifyAllocators ds sis allocatorSummary escapeSummary finalizerSummary
                 , identifyRefCounting ds refCountSummary finalizerSummary scalarEffectSummary
                 ]
      analysisFunction = callGraphComposeAnalysis analyses
      analysisResult =
        parallelCallGraphSCCTraversal cg analysisFunction mempty

      diags = mconcat $ extractSummary analysisResult (getL diagnosticLens)
      summaries = extractSummary analysisResult ModuleSummary

  case formatDiagnostics (diagnosticLevel opts) diags of
    Nothing -> return ()
    Just diagString -> putStrLn diagString

  -- Persist the module summary
  saveModule repo name deps m summaries ds
  case (reportDir opts, librarySource opts) of
    (Nothing, _) -> return ()
    (Just d, Nothing) -> writeSummary m summaries ds d
    (Just d, Just archive) -> writeDetailedReport m summaries ds d archive

writeSummary :: Module -> [ModuleSummary] -> DependencySummary -> FilePath -> IO ()
writeSummary m summaries ds rDir = do
  let rep = compileSummaryReport m summaries ds
  writeHTMLSummary rep rDir

-- | Called when a source tarball was provided.  This generates and
-- writes the report for the Module in the location specified by the
-- user.
writeDetailedReport :: Module -> [ModuleSummary] -> DependencySummary -> FilePath -> FilePath -> IO ()
writeDetailedReport m summaries ds rDir fp = do
  arc <- readArchive fp
  let rep = compileDetailedReport m arc summaries ds
  writeHTMLReport rep rDir
