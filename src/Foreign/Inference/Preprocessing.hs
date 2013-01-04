{-# LANGUAGE TemplateHaskell #-}
-- | This module defines helpers to preprocess bitcode into an
-- acceptable form.  This mostly means deciding which optimizations to
-- run to make analysis easier.
module Foreign.Inference.Preprocessing (
  requiredOptimizations
  ) where

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
                        , "-gvn"     -- Unifies identical values
                        , "-basicaa" -- Disambiguates trivial aliases
                        , "-disable-inlining"
                        ]
