{-# LANGUAGE RankNTypes #-}
-- | This anaysis identifies functions that have scalar effects on
-- their arguments.
--
-- This refers to functions that increment or decrement struct fields
-- of pointer parameters.  It is mainly used by the reference counting
-- analysis.  This is mostly useful for libraries that perform their
-- increments and decrements via function calls instead of directly
-- doing the operations in the incref/decref functions.  A few
-- libraries (like dbus) do this to encapsulate the details of atomic
-- increments.
module Foreign.Inference.Analysis.ScalarEffects (
  ScalarEffectSummary,
  identifyScalarEffects,
  scalarEffectAddOne,
  scalarEffectSubOne
  ) where

import Control.DeepSeq
import Control.Lens
import Control.Monad.Identity
import qualified Data.HashMap.Strict as HM
import Data.Monoid

import LLVM.Analysis
import LLVM.Analysis.AccessPath
import LLVM.Analysis.CFG
import LLVM.Analysis.CallGraphSCCTraversal
import LLVM.Analysis.ScalarEffects

import Foreign.Inference.Diagnostics
import Foreign.Inference.Interface

data ScalarEffectSummary = ScalarEffectSummary !ScalarEffectResult
                         deriving (Eq)

instance HasDiagnostics ScalarEffectSummary

instance Monoid ScalarEffectSummary where
  mempty = ScalarEffectSummary mempty
  mappend (ScalarEffectSummary s1) (ScalarEffectSummary s2) =
    ScalarEffectSummary (s1 `mappend` s2)

instance NFData ScalarEffectSummary where
  rnf e@(ScalarEffectSummary s) =
    s `deepseq` e `seq` ()

instance SummarizeModule ScalarEffectSummary where
  summarizeFunction _ _ = []
  summarizeArgument = summarizeEffectArgument

summarizeEffectArgument :: Argument -> ScalarEffectSummary -> [(ParamAnnotation, [Witness])]
summarizeEffectArgument a (ScalarEffectSummary s) =
  case HM.lookup a s of
    Nothing -> []
    Just (EffectAdd1 (AbstractAccessPath t _ ats)) ->
      [(PAScalarEffectAddOne (show t) ats, [])]
    Just (EffectSub1 (AbstractAccessPath t _ ats)) ->
      [(PAScalarEffectSubOne (show t) ats, [])]

identifyScalarEffects :: (FuncLike funcLike, HasCFG funcLike, HasFunction funcLike)
                         => Simple Lens compositeSummary ScalarEffectSummary
                         -> ComposableAnalysis compositeSummary funcLike
identifyScalarEffects lns =
  composableAnalysisM runIdentity analysisWrapper lns
  where
    analysisWrapper f (ScalarEffectSummary s) = do
      res <- scalarEffectAnalysis f s
      return $! ScalarEffectSummary res

scalarEffectAddOne :: ScalarEffectSummary -> Argument -> Maybe AbstractAccessPath
scalarEffectAddOne (ScalarEffectSummary s) a =
  case HM.lookup a s of
    Nothing -> Nothing
    Just (EffectAdd1 accPath) -> Just accPath
    _ -> Nothing

scalarEffectSubOne :: ScalarEffectSummary -> Argument -> Maybe AbstractAccessPath
scalarEffectSubOne (ScalarEffectSummary s) a =
  case HM.lookup a s of
    Nothing -> Nothing
    Just (EffectSub1 accPath) -> Just accPath
    _ -> Nothing
