{-# LANGUAGE RankNTypes #-}
module Main ( main ) where

import Control.DeepSeq
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

import Data.LLVM
import Data.LLVM.Analysis.CFG
import Data.LLVM.Analysis.CallGraph
import Data.LLVM.Analysis.CallGraphSCCTraversal
import Data.LLVM.Analysis.PointsTo.TrivialFunction
import Data.LLVM.Parse

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
import Foreign.Inference.Analysis.Return

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
                  , wantsHelp = False
                  }


showHelpAndExit :: Mode a -> IO b -> IO b
showHelpAndExit arguments exitCmd = do
  putStrLn $ showText (Wrap 80) $ helpText [] HelpFormatOne arguments
  exitCmd

data FunctionMetadata =
  FunctionMetadata { functionOriginal :: Function
                   , functionCFG :: CFG
                   }

instance HasFunction FunctionMetadata where
  getFunction = functionOriginal

instance HasCFG FunctionMetadata where
  getCFG = functionCFG

instance FuncLike FunctionMetadata where
  convertFunction f =
    FunctionMetadata { functionOriginal = f
                     , functionCFG = mkCFG f
                     }

data AnalysisSummary =
  AnalysisSummary { _nullableSummary :: NullableSummary
                  , _outputSummary :: OutputSummary
                  , _arraySummary :: ArraySummary
                  , _returnSummary :: ReturnSummary
                  , _finalizerSummary :: FinalizerSummary
                  , _escapeSummary :: EscapeSummary
                  , _allocatorSummary :: AllocatorSummary
                  }
  deriving (Eq)

instance NFData AnalysisSummary where
  rnf a@(AnalysisSummary s1 s2 s3 s4 s5 s6 s7) =
    s1 `deepseq` s2 `deepseq` s3 `deepseq` s4 `deepseq` s5
      `deepseq` s6 `deepseq` s7 `deepseq` a `seq` ()

nullableSummary = lens _nullableSummary (\x s -> s { _nullableSummary = x })
outputSummary = lens _outputSummary (\x s -> s { _outputSummary = x })
arraySummary = lens _arraySummary (\x s -> s { _arraySummary = x })
returnSummary = lens _returnSummary (\x s -> s { _returnSummary = x })
finalizerSummary = lens _finalizerSummary (\x s -> s { _finalizerSummary = x })
escapeSummary = lens _escapeSummary (\x s -> s { _escapeSummary = x })
allocatorSummary = lens _allocatorSummary (\x s -> s { _allocatorSummary = x })

instance Monoid AnalysisSummary where
  mempty = AnalysisSummary mempty mempty mempty mempty mempty mempty mempty
  mappend a1 a2 =
    AnalysisSummary { _nullableSummary = _nullableSummary a1 `mappend` _nullableSummary a2
                    , _outputSummary = _outputSummary a1 `mappend` _outputSummary a2
                    , _arraySummary = _arraySummary a1 `mappend` _arraySummary a2
                    , _returnSummary = _returnSummary a1 `mappend` _returnSummary a2
                    , _finalizerSummary = _finalizerSummary a1 `mappend` _finalizerSummary a2
                    , _escapeSummary = _escapeSummary a1 `mappend` _escapeSummary a2
                    , _allocatorSummary = _allocatorSummary a1 `mappend` _allocatorSummary a2
                    }

extractSummary :: AnalysisSummary ->
                  (forall a . (HasDiagnostics a, SummarizeModule a) =>  a -> b)
                  -> [b]
extractSummary summ f =
  [ f (_nullableSummary summ)
  , f (_outputSummary summ)
  , f (_arraySummary summ)
  , f (_returnSummary summ)
  , f (_finalizerSummary summ)
  , f (_escapeSummary summ)
  , f (_allocatorSummary summ)
  ]

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
  ds <- loadDependencies [repo] deps

  let analyses :: [ComposableAnalysis AnalysisSummary FunctionMetadata]
      analyses = [ identifyReturns ds returnSummary
                 , identifyArrays ds arraySummary
                 , identifyFinalizers ds finalizerSummary
                 , identifyEscapes ds escapeSummary
                 , identifyOutput ds outputSummary
                 , identifyNullable ds nullableSummary returnSummary
                 , identifyAllocators ds allocatorSummary escapeSummary
                 ]
      analysisFunction = composableAnalysis analyses
      analysisResult =
        parallelCallGraphSCCTraversal cg analysisFunction mempty

      diags = mconcat $ extractSummary analysisResult getDiagnostics
      summaries = extractSummary analysisResult ModuleSummary

  case formatDiagnostics (diagnosticLevel opts) diags of
    Nothing -> return ()
    Just diagString -> putStrLn diagString

  -- Persist the module summary
  saveModule repo name deps m summaries
  -- Write out a report if requested
  let defaultRepDir = repo </> name
  maybe (return ()) (writeReport opts m summaries defaultRepDir) (librarySource opts)

-- | Called when a source tarball was provided.  This generates and
-- writes the report for the Module in the location specified by the
-- user.
writeReport :: Opts -> Module -> [ModuleSummary] -> FilePath -> FilePath -> IO ()
writeReport opts m summaries defDir fp = do
  arc <- readArchive fp
  let rep = compileReport m arc summaries
      repDir = maybe defDir id (reportDir opts)
  writeHTMLReport rep repDir
