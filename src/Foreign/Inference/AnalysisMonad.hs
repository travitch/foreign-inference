{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Foreign.Inference.AnalysisMonad (
  AnalysisMonad,
  HasDiagnostics(..),
  runAnalysis,
  module Control.Monad.RWS.Strict
  ) where

import Control.Monad.RWS.Strict
import Foreign.Inference.Diagnostics

newtype AnalysisMonad env state a =
  AnalysisMonad { unAnalysis :: RWS env Diagnostics state a }
  deriving (Monad,
            MonadState state,
            MonadReader env,
            MonadWriter Diagnostics)

class HasDiagnostics a where
  addDiagnostics :: a -> Diagnostics -> a
  addDiagnostics a _ = a

  getDiagnostics :: a -> Diagnostics
  getDiagnostics _ = mempty

-- Add a context on a here that forces a to implement an "attach
-- diags" function so we can stuff the diagnostics into the result and
-- just return that single value.
runAnalysis :: (HasDiagnostics a) => AnalysisMonad env state a -> env -> state -> a
runAnalysis analysis env state = addDiagnostics res diags
  where
    (res, diags) = evalRWS (unAnalysis analysis) env state
