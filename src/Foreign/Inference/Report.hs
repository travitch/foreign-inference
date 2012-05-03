{-# LANGUAGE OverloadedStrings, TemplateHaskell #-}
-- | This module provides some functions to generate HTML reports for
-- a Module and its inferred annotations.  This module handles the
-- extraction of source code (from tarballs/zip files) and mapping
-- Functions to their associated source code using various heuristics.
--
-- FIXME: The drilldowns for functions may be overwritten by functions
-- of the same name... this probably won't be a problem in practice
-- since there would be linker errors of that happens.
module Foreign.Inference.Report (
  -- * Types
  InterfaceReport,
  -- * Functions
  compileDetailedReport,
  compileSummaryReport,
  writeHTMLReport,
  writeHTMLSummary
  ) where

import GHC.Conc ( getNumCapabilities )

import Control.Concurrent.ParallelIO.Local
import Data.ByteString.Lazy.Char8 ( ByteString )
import qualified Data.ByteString.Char8 as BS8
import qualified Data.ByteString.Lazy as LBS
import Data.FileEmbed
import qualified Data.Map as M
import System.Directory ( createDirectoryIfMissing )
import System.FilePath
import Text.Blaze.Html.Renderer.Utf8 ( renderHtml )

import Codec.Archive
import LLVM.Analysis
import Foreign.Inference.Interface
import Foreign.Inference.Report.FunctionText
import Foreign.Inference.Report.Html
import Foreign.Inference.Report.Types

highlightJs :: (FilePath, BS8.ByteString)
highlightJs = ("highlight.js", $(embedFile "static/highlight.js"))
codeCss :: (FilePath, BS8.ByteString)
codeCss = ("hk-tango.css", $(embedFile "static/hk-tango.css"))
jqueryJs :: (FilePath, BS8.ByteString)
jqueryJs = ("jquery-1.7.1.js", $(embedFile "static/jquery-1.7.1.js"))
styleCss :: (FilePath, BS8.ByteString)
styleCss = ("style.css", $(embedFile "static/style.css"))

staticFiles :: [(FilePath, BS8.ByteString)]
staticFiles = [ codeCss, styleCss, highlightJs, jqueryJs ]


-- | Write the given report into the given directory.  An index.html file
-- will be placed in the directory and subdirectories within that will
-- contain the actual content.
--
-- An error will be thrown if the given path exists and is not a
-- directory.  The directory will be created if it does not exist.
writeHTMLReport :: InterfaceReport -> FilePath -> IO ()
writeHTMLReport r dir = do
  let indexFile = dir </> "index.html"
      indexPage = htmlIndexPage r [LinkDrilldowns]

  -- Create the directory tree for the report
  createDirectoryIfMissing True dir
  createDirectoryIfMissing True (dir </> "functions")

  -- Write out an index page
  LBS.writeFile indexFile (renderHtml indexPage)

  -- Write out the individual function listings.  Since highlighting
  -- each function is completely independent we run them in parallel
  -- with as many processors as are available.
  caps <- getNumCapabilities
  let bodyPairs = M.toList (reportFunctionBodies r)
      actions = map (writeFunctionBodyPage r dir) bodyPairs
  withPool caps $ \p -> parallel_ p actions

  -- Copy over static resources (like css and js)
  mapM_ (installStaticFile dir) staticFiles


-- | This is like 'writeHTMLReport', except it only writes out the
-- top-level overview HTML page.  The per-function breakdowns are not
-- generated.
writeHTMLSummary :: InterfaceReport -> FilePath -> IO ()
writeHTMLSummary r dir = do
  let indexFile = dir </> "index.html"
      indexPage = htmlIndexPage r []

  -- Create the directory tree for the report
  createDirectoryIfMissing True dir

  -- Write out an index page
  LBS.writeFile indexFile (renderHtml indexPage)

  -- Copy over static resources (like css and js)
  mapM_ (installStaticFile dir) staticFiles

-- | Install a file from the project share directory to the target
-- report directory (top-level).
installStaticFile :: FilePath -> (FilePath, BS8.ByteString) -> IO ()
installStaticFile dir (name, content) =
  BS8.writeFile (dir </> name) content

writeFunctionBodyPage :: InterfaceReport
                         -> FilePath
                         -> (Function, (FilePath, Int, ByteString))
                         -> IO ()
writeFunctionBodyPage r dir (f, (srcFile, startLine, body)) = do
  let funcName = BS8.unpack (identifierContent (functionName f))
      filename = dir </> "functions" </> funcName <.> "html"
      functionPage = htmlFunctionPage r f srcFile startLine body

  LBS.writeFile filename (renderHtml functionPage)

-- | Given a Module, the properties that have been inferred about it,
-- and an archive of its source, make a best-effort to construct an
-- informative report of the results.
compileDetailedReport :: Module -> ArchiveIndex -> [ModuleSummary] -> DependencySummary -> InterfaceReport
compileDetailedReport m a = InterfaceReport m bodies a
  where
    fs = moduleDefinedFunctions m
    bodies = foldr bodyExtractor M.empty fs
    bodyExtractor f acc =
      case getFunctionText a f of
        Nothing -> acc
        Just b -> M.insert f b acc

compileSummaryReport :: Module -> [ModuleSummary] -> DependencySummary -> InterfaceReport
compileSummaryReport = InterfaceSummaryReport