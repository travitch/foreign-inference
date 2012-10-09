{-# LANGUAGE OverloadedStrings, CPP #-}
#if defined(RELOCATE)
{-# LANGUAGE TemplateHaskell #-}
#endif
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
import qualified Data.ByteString.Lazy as LBS
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

#if defined(RELOCATE)
import Data.FileEmbed
import qualified Data.ByteString as BS

staticFiles :: [(FilePath, BS.ByteString)]
staticFiles = $(embedDir "static")

-- | Install a file from the project share directory to the target
-- report directory (top-level).
installStaticFiles :: FilePath -> IO ()
installStaticFiles dst = do
  let install (name, content) = BS.writeFile (dst </> name) content
  mapM_ install staticFiles

#else
import System.Directory ( copyFile, getDirectoryContents )

import Paths_foreign_inference

installStaticFiles :: FilePath -> IO ()
installStaticFiles dst = do
  src <- getDataDir
  files <- getDirectoryContents (src </> "static")
  let doCopy f = do
        case f == "." || f == ".." of
          True -> return ()
          False -> copyFile (src </> "static" </> f) (dst </> f)
  mapM_ doCopy files

#endif



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
  installStaticFiles dir


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
  installStaticFiles dir

writeFunctionBodyPage :: InterfaceReport
                         -> FilePath
                         -> (Function, (FilePath, Int, ByteString))
                         -> IO ()
writeFunctionBodyPage r dir (f, (srcFile, startLine, body)) = do
  let funcName = identifierAsString (functionName f)
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