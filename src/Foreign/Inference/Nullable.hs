{-# LANGUAGE ViewPatterns #-}
-- | This module defines a Nullable pointer analysis
--
-- Nullable pointers are those pointers that are checked against NULL
-- before they are used.
module Foreign.Inference.Nullable (
  NullableSummary,
  identifyNullable
  ) where

import Data.Map ( Map )
import qualified Data.Map as M
import Data.Maybe ( mapMaybe )
import Data.Set ( Set )
import qualified Data.Set as S

import Data.LLVM
import Data.LLVM.CallGraph
import Data.LLVM.Analysis.CallGraphSCCTraversal
import Data.LLVM.Analysis.Dataflow
import Data.LLVM.Analysis.Escape

type NullableSummary = Set Argument

identifyNullable :: CallGraph -> EscapeResult -> NullableSummary
identifyNullable cg er = callGraphSCCTraversal cg (nullableAnalysis er) S.empty

nullableAnalysis = undefined