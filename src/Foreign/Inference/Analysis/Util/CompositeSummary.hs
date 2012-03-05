{-# LANGUAGE RankNTypes, TemplateHaskell #-}
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
  extractSummary
  ) where

import Control.DeepSeq
import Data.Lens.Template
import Data.Monoid

import LLVM.Analysis
import LLVM.Analysis.Types
import LLVM.Analysis.CFG

import Foreign.Inference.Analysis.Allocator
import Foreign.Inference.Analysis.Array
import Foreign.Inference.Analysis.Escape
import Foreign.Inference.Analysis.Finalize
import Foreign.Inference.Analysis.Nullable
import Foreign.Inference.Analysis.Output
import Foreign.Inference.Analysis.Return
import Foreign.Inference.Diagnostics
import Foreign.Inference.Interface

-- | The value we derive from each function during the call graph
-- traversal.  For now, it just adds a CFG.
data FunctionMetadata =
  FunctionMetadata { functionOriginal :: Function
                   , functionCFG :: CFG
                   }

instance HasFunction FunctionMetadata where
  getFunction = functionOriginal

instance HasCFG FunctionMetadata where
  getCFG = functionCFG

instance FuncLike FunctionMetadata where
  fromFunction f =
    FunctionMetadata { functionOriginal = f
                     , functionCFG = mkCFG f
                     }

-- | A type containing all of the sub-summaries.
data AnalysisSummary =
  AnalysisSummary { _nullableSummary :: !NullableSummary
                  , _outputSummary :: !OutputSummary
                  , _arraySummary :: !ArraySummary
                  , _returnSummary :: !ReturnSummary
                  , _finalizerSummary :: !FinalizerSummary
                  , _escapeSummary :: !EscapeSummary
                  , _allocatorSummary :: !AllocatorSummary
                  }
  deriving (Eq)

$(makeLens ''AnalysisSummary)

instance NFData AnalysisSummary where
  rnf a@(AnalysisSummary s1 s2 s3 s4 s5 s6 s7) =
    s1 `deepseq` s2 `deepseq` s3 `deepseq` s4 `deepseq` s5
      `deepseq` s6 `deepseq` s7 `deepseq` a `seq` ()

instance Monoid AnalysisSummary where
  mempty = AnalysisSummary mempty mempty mempty mempty mempty mempty mempty
  mappend a1 a2 =
    AnalysisSummary { _nullableSummary = _nullableSummary a1 `mappend` _nullableSummary a2
                    , _outputSummary = _outputSummary a1 `mappend` _outputSummary a2
                    , _arraySummary = _arraySummary a1 `mappend` _arraySummary a2
                    , _returnSummary = _returnSummary a1 `mappend` _returnSummary a2
                    , _finalizerSummary = _finalizerSummary a1 `mappend` _finalizerSummary a2
                    , _escapeSummary = _escapeSummary a1 `mappend` _escapeSummary a2
                    , _allocatorSummary = _allocatorSummary a1 `mappend` _allocatorSummary a2
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
  ]
