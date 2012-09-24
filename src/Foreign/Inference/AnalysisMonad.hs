{-# LANGUAGE GeneralizedNewtypeDeriving, NoMonomorphismRestriction #-}
module Foreign.Inference.AnalysisMonad (
  AnalysisMonad,
  runAnalysis,
  analysisEnvironment,
  analysisLocal,
  analysisGet,
  analysisPut
  ) where

import Control.Lens
import Control.Monad.RWS.Strict

import Foreign.Inference.Diagnostics

newtype AnalysisMonad env st a =
  AnalysisMonad { unAnalysis :: RWS env Diagnostics st a }
  deriving (Monad,
            MonadState st,
            MonadReader env,
            MonadWriter Diagnostics)

analysisEnvironment :: (MonadReader r m) => (r -> a) -> m a
analysisEnvironment = asks

analysisLocal :: (MonadReader r m) => (r -> r) -> m a -> m a
analysisLocal = local

analysisGet :: (MonadState s m) => m s
analysisGet = get

analysisPut :: (MonadState s m) => s -> m ()
analysisPut = put

addDiagnostics :: HasDiagnostics a => a -> Diagnostics -> a
addDiagnostics res newDiags =
  set diagnosticLens (curDiags `mappend` newDiags) res
  where
    curDiags = view diagnosticLens res

-- Add a context on a here that forces a to implement an "attach
-- diags" function so we can stuff the diagnostics into the result and
-- just return that single value.
runAnalysis :: (HasDiagnostics a) => AnalysisMonad env state a -> env -> state -> a
runAnalysis analysis env s = addDiagnostics res diags
  where
    (res, diags) = evalRWS (unAnalysis analysis) env s
