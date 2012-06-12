{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Foreign.Inference.AnalysisMonad (
  AnalysisMonad,
  runAnalysis,
  module Control.Monad.RWS.Strict
  ) where

import Control.Monad.RWS.Strict
import Data.Lens.Common

import Foreign.Inference.Diagnostics

newtype AnalysisMonad env st a =
  AnalysisMonad { unAnalysis :: RWS env Diagnostics st a }
  deriving (Monad,
            MonadState st,
            MonadReader env,
            MonadWriter Diagnostics)

addDiagnostics :: HasDiagnostics a => a -> Diagnostics -> a
addDiagnostics res newDiags =
  setL diagnosticLens (curDiags `mappend` newDiags) res
  where
    curDiags = getL diagnosticLens res

-- Add a context on a here that forces a to implement an "attach
-- diags" function so we can stuff the diagnostics into the result and
-- just return that single value.
runAnalysis :: (HasDiagnostics a) => AnalysisMonad env state a -> env -> state -> a
runAnalysis analysis env state = addDiagnostics res diags
  where
    (res, diags) = evalRWS (unAnalysis analysis) env state
