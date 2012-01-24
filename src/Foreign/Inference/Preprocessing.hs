{-# LANGUAGE TemplateHaskell #-}
-- | This module defines helpers to preprocess bitcode into an
-- acceptable form.  This mostly means deciding which optimizations to
-- run to make analysis easier.
module Foreign.Inference.Preprocessing (
  readBitcode,
  requiredOptimizations
  ) where

import Control.Monad ( when )

import FileLocation

import System.Exit ( ExitCode(ExitSuccess) )
import System.FilePath
import System.IO.Temp
import System.Process

import Data.LLVM
import Data.LLVM.Environment

-- | These are the options that the analysis relies on to work.  It
-- invokes opt with these options to preprocess input bitcode.
--
-- This may need to vary by LLVM version as the optimizations evolve.
--
-- This strikes a balance between removing memory references (with
-- mem2reg) and optimizing away useful information (like coalescing
-- branch conditions with no side effects).
--
-- This also disables inlining.  Inlining can give some extra
-- information but can also do confusing things (not to mention
-- blowing up the IR)
requiredOptimizations :: [String]
requiredOptimizations = [ "-mem2reg" -- Promotes memory references to registers
                        -- , "-gvn"     -- Unifies identical values
                        , "-basicaa" -- Disambiguates trivial aliases
                        , "-disable-inlining"
                        ]

-- | A wrapper around parseLLVMFile that first optimizes the bitcode
-- using opt and the required optimizations.
readBitcode :: (FilePath -> IO (Either String Module))
               -> FilePath -> IO (Either String Module)
readBitcode parseFile fp =
  withSystemTempFile ("opt_" ++ takeFileName fp) $ \optFname _ -> do
    opt <- findOpt
    let optCmd = proc opt ("-o" : optFname : fp : requiredOptimizations)
    (_, _, _, p) <- createProcess optCmd
    rc <- waitForProcess p
    when (rc /= ExitSuccess) ($err' ("Could not optimize bitcode: " ++ fp))
    parseFile optFname
