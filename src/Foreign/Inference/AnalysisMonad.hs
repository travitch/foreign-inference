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
import Foreign.Inference.Interface

data Env env = Env { envDependencies :: DependencySummary
                   , envEnv :: env
                   }

newtype AnalysisMonad env st a =
  AnalysisMonad { unAnalysis :: RWS (Env env) Diagnostics st a }
  deriving (Monad,
            MonadState st,
            MonadReader (Env env),
            MonadWriter Diagnostics)

instance HasDependencies (AnalysisMonad env st) where
  getDependencySummary = asks envDependencies

analysisEnvironment :: (env -> a) -> AnalysisMonad env st a
analysisEnvironment r = asks envEnv >>= (return . r)

analysisLocal :: (env -> env) -> AnalysisMonad env st a -> AnalysisMonad env st a
analysisLocal r = local (\(Env d e) -> Env d (r e))

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
runAnalysis :: (HasDiagnostics a) => AnalysisMonad env state a -> DependencySummary -> env -> state -> a
runAnalysis analysis ds env s = addDiagnostics res diags
  where
    (res, diags) = evalRWS (unAnalysis analysis) (Env ds env) s
