{-# LANGUAGE RankNTypes, TemplateHaskell, DeriveGeneric #-}
{-| This module defines a data type that can be used as the summary
type for a composite analysis using all of the analyses defined in
this package.

It is useful to have it defined in a common module so it can be
re-used for all of the tests and the driver program.

Additionally, moving it to the library (instead of duplicating it in
each executable) makes it easier to use TemplateHaskell here to
generate lenses.

-}
module Foreign.Inference.Analysis.Util.CompositeSummary (
  FunctionMetadata(..),
  AnalysisSummary(..),
  nullableSummary,
  outputSummary,
  arraySummary,
  returnSummary,
  finalizerSummary,
  escapeSummary,
  allocatorSummary,
  refCountSummary,
  scalarEffectSummary,
  errorHandlingSummary,
  transferSummary,
  extractSummary
  ) where

import GHC.Generics

import Control.DeepSeq
import Control.DeepSeq.Generics
import Control.Lens
import Data.Monoid

import LLVM.Analysis
import LLVM.Analysis.BlockReturnValue
import LLVM.Analysis.Dominance
import LLVM.Analysis.CDG
import LLVM.Analysis.CFG
import LLVM.Analysis.Types

import Foreign.Inference.Analysis.Allocator
import Foreign.Inference.Analysis.Array
import Foreign.Inference.Analysis.ErrorHandling
import Foreign.Inference.Analysis.Escape
import Foreign.Inference.Analysis.Finalize
import Foreign.Inference.Analysis.Nullable
import Foreign.Inference.Analysis.Output
import Foreign.Inference.Analysis.RefCount
import Foreign.Inference.Analysis.Return
import Foreign.Inference.Analysis.ScalarEffects
import Foreign.Inference.Analysis.Transfer
import Foreign.Inference.Diagnostics
import Foreign.Inference.Interface

-- | The value we derive from each function during the call graph
-- traversal.  For now, it just adds a CFG.
data FunctionMetadata =
  FunctionMetadata { functionOriginal :: Function
                   , functionCFG :: CFG
                   , functionCDG :: CDG
                   , functionDomTree :: DominatorTree
                   , functionPostdomTree :: PostdominatorTree
                   , functionBlockReturns :: BlockReturns
                   }

instance HasBlockReturns FunctionMetadata where
  getBlockReturns = functionBlockReturns

instance HasFunction FunctionMetadata where
  getFunction = functionOriginal

instance HasCFG FunctionMetadata where
  getCFG = functionCFG

instance HasDomTree FunctionMetadata where
  getDomTree = functionDomTree

instance HasPostdomTree FunctionMetadata where
  getPostdomTree = functionPostdomTree

instance FuncLike FunctionMetadata where
  fromFunction f =
    FunctionMetadata { functionOriginal = f
                     , functionCFG = cfg
                     , functionCDG = controlDependenceGraph cfg
                     , functionDomTree = dominatorTree cfg
                     , functionPostdomTree = postdominatorTree (reverseCFG cfg)
                     , functionBlockReturns = labelBlockReturns cfg
                     }
    where
      cfg = mkCFG f

instance HasCDG FunctionMetadata where
  getCDG = functionCDG

-- | A type containing all of the sub-summaries.
data AnalysisSummary =
  AnalysisSummary { _nullableSummary :: !NullableSummary
                  , _outputSummary :: !OutputSummary
                  , _arraySummary :: !ArraySummary
                  , _returnSummary :: !ReturnSummary
                  , _finalizerSummary :: !FinalizerSummary
                  , _escapeSummary :: !EscapeSummary
                  , _allocatorSummary :: !AllocatorSummary
                  , _refCountSummary :: !RefCountSummary
                  , _scalarEffectSummary :: !ScalarEffectSummary
                  , _errorHandlingSummary :: !ErrorSummary
                  , _transferSummary :: !TransferSummary
                  }
  deriving (Eq, Generic)

$(makeLenses ''AnalysisSummary)

instance NFData AnalysisSummary where
  rnf = genericRnf

instance Monoid AnalysisSummary where
  mempty = AnalysisSummary { _nullableSummary = mempty
                           , _outputSummary = mempty
                           , _arraySummary = mempty
                           , _returnSummary = mempty
                           , _finalizerSummary = mempty
                           , _escapeSummary = mempty
                           , _allocatorSummary = mempty
                           , _refCountSummary = mempty
                           , _scalarEffectSummary = mempty
                           , _errorHandlingSummary = mempty
                           , _transferSummary = mempty
                           }
  mappend a1 a2 =
    AnalysisSummary { _nullableSummary = _nullableSummary a1 `mappend` _nullableSummary a2
                    , _outputSummary = _outputSummary a1 `mappend` _outputSummary a2
                    , _arraySummary = _arraySummary a1 `mappend` _arraySummary a2
                    , _returnSummary = _returnSummary a1 `mappend` _returnSummary a2
                    , _finalizerSummary = _finalizerSummary a1 `mappend` _finalizerSummary a2
                    , _escapeSummary = _escapeSummary a1 `mappend` _escapeSummary a2
                    , _allocatorSummary = _allocatorSummary a1 `mappend` _allocatorSummary a2
                    , _refCountSummary = _refCountSummary a1 `mappend` _refCountSummary a2
                    , _scalarEffectSummary = _scalarEffectSummary a1 `mappend` _scalarEffectSummary a2
                    , _errorHandlingSummary = _errorHandlingSummary a1 `mappend` _errorHandlingSummary a2
                    , _transferSummary = _transferSummary a1 `mappend` _transferSummary a2
                    }

-- | Apply a function that uniformly summarizes *all* of the
-- individual analysis summaries.  Uses so far are extracting
-- diagnostics and producing module summaries.
extractSummary :: AnalysisSummary ->
                  (forall a . (HasDiagnostics a, SummarizeModule a) => a -> b)
                  -> [b]
extractSummary summ f =
  [ f (_nullableSummary summ)
  , f (_outputSummary summ)
  , f (_arraySummary summ)
  , f (_returnSummary summ)
  , f (_finalizerSummary summ)
  , f (_escapeSummary summ)
  , f (_allocatorSummary summ)
  , f (_refCountSummary summ)
  , f (_scalarEffectSummary summ)
  , f (_errorHandlingSummary summ)
  , f (_transferSummary summ)
  ]
