{-# LANGUAGE DeriveGeneric, TemplateHaskell #-}
{-# LANGUAGE RankNTypes #-}
module Foreign.Inference.Analysis.Transfer (
  TransferSummary,
  identifyTransfers
  ) where

import GHC.Generics ( Generic )

import Control.DeepSeq
import Control.DeepSeq.Generics ( genericRnf )
import Control.Lens ( Simple, Lens, makeLenses )
import Data.Monoid

import LLVM.Analysis
import LLVM.Analysis.CallGraphSCCTraversal

import Foreign.Inference.AnalysisMonad
import Foreign.Inference.Diagnostics
import Foreign.Inference.Interface
import Foreign.Inference.Analysis.IndirectCallResolver

data TransferSummary = TransferSummary { _transferDiagnostics :: Diagnostics
                                       }
                     deriving (Generic)

$(makeLenses ''TransferSummary)

instance Eq TransferSummary where
  (TransferSummary _) == (TransferSummary _) = True

instance Monoid TransferSummary where
  mempty = TransferSummary mempty
  mappend (TransferSummary d1) (TransferSummary d2) =
    TransferSummary (d1 `mappend` d2)

instance NFData TransferSummary where
  rnf = genericRnf

instance HasDiagnostics TransferSummary where
  diagnosticLens = transferDiagnostics

instance SummarizeModule TransferSummary where
  summarizeFunction _ _ = []
  summarizeArgument _ _ = []

identifyTransfers :: (HasFunction funcLike)
                     => [funcLike]
                     -> DependencySummary
                     -> IndirectCallSummary
                     -> compositeSummary
                     -> Simple Lens compositeSummary TransferSummary
                     -> compositeSummary
identifyTransfers funcLikes ds pta p1res tlens = undefined
