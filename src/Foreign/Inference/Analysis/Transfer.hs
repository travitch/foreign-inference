{-# LANGUAGE DeriveGeneric, TemplateHaskell, ViewPatterns #-}
{-# LANGUAGE RankNTypes #-}
module Foreign.Inference.Analysis.Transfer (
  TransferSummary,
  identifyTransfers
  ) where

import GHC.Generics ( Generic )

import Control.DeepSeq
import Control.DeepSeq.Generics ( genericRnf )
import Control.Lens ( (^.), Simple, makeLenses )
import Data.List ( find )
import Data.Maybe ( fromMaybe, mapMaybe )
import Data.Monoid
import Data.Set ( Set )
import qualified Data.Set as S

import LLVM.Analysis
import LLVM.Analysis.AccessPath
import LLVM.Analysis.CallGraphSCCTraversal
import LLVM.Analysis.PointsTo

import Foreign.Inference.AnalysisMonad
import Foreign.Inference.Diagnostics
import Foreign.Inference.Interface
import Foreign.Inference.Analysis.Finalize
import Foreign.Inference.Analysis.IndirectCallResolver

import Debug.Trace
debug = flip trace

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

-- Algorithm:
--
-- In one pass, determine all of the *structure fields* that are
-- passed to a finalizer.  These are *owned* fields.  The shape
-- analysis bit will come later (to find finalized things that are
-- stored in "container-likes")
--
-- Maybe we can remove the need for some shape analysis by looking at
-- dependence.
--
-- > void foo(bar * baz) {
-- >   while(hasNext(baz->quux)) {
-- >     q = next(&baz->quux);
-- >     free_quux(q);
-- >   }
-- > }
--
-- In a second pass, find all of the arguments that flow into those
-- owned fields and mark them as Transferred.  Again, this will need
-- to be aware of the pseudo-shape analysis results (i.e., this
-- parameter ends up linked into this data structure via this field
-- after this call).  This pass will need to reach a fixed point.
--
-- At the end of the day, this will be simpler than the escape
-- analysis since we do not need to track fields of arguments or
-- anything of that form.
--
-- This could additionally depend on the ref count analysis and just
-- strip off transfer tags from ref counted types.

identifyTransfers :: (HasFunction funcLike)
                     => [funcLike]
                     -> DependencySummary
                     -> IndirectCallSummary
                     -> compositeSummary
                     -> Simple Lens compositeSummary FinalizerSummary
                     -> Simple Lens compositeSummary TransferSummary
                     -> compositeSummary
identifyTransfers funcLikes ds pta p1res flens tlens =
  p1res `debug` show ownedFields
  where
    finSumm = p1res ^. flens
    ownedFields = foldr (identifyOwnedFields ds pta finSumm) mempty funcLikes

-- | Add any field passed to a known finalizer to the accumulated Set.
--
-- This will eventually need to incorporate shape analysis results.
-- It will also need to distinguish somehow between fields that are
-- finalized and elements of container fields that are finalized.
identifyOwnedFields :: (HasFunction funcLike)
                       => DependencySummary
                       -> IndirectCallSummary
                       -> FinalizerSummary
                       -> funcLike
                       -> Set AbstractAccessPath
                       -> Set AbstractAccessPath
identifyOwnedFields ds pta finSumm funcLike ownedFields =
  foldr checkFinalize ownedFields insts
  where
    insts = functionInstructions (getFunction funcLike)
    checkFinalize i acc =
      case i of
        CallInst { callFunction = cf, callArguments = (map fst -> args) } ->
          checkCall cf args acc
        InvokeInst { invokeFunction = cf, invokeArguments = (map fst -> args) } ->
          checkCall cf args acc
        _ -> acc
    checkCall cf args acc =
      let nargs = length args
      in case mapFirst (isFinalizer nargs) (pointsToWrapper pta cf) of
        Nothing -> acc
        Just finIx ->
          let actual = args !! finIx
          in case valueContent' actual of
            InstructionC i -> fromMaybe acc $ do
              accPath <- accessPath i
              let absPath = abstractAccessPath accPath
              return $ S.insert absPath acc
            _ -> acc
    isFinalizer nargs callee =
      find (formalHasFinalizeAnnot callee) [0..(nargs-1)]
    formalHasFinalizeAnnot callee argIx = fromMaybe False $ do
      annots <- lookupArgumentSummary ds finSumm callee argIx
      return $ PAFinalize `elem` annots

-- | A wrapper around the points-to analysis that just returns the
-- input callee for direct calls.
pointsToWrapper :: (PointsToAnalysis a) => a -> Value -> [Value]
pointsToWrapper pta cf =
  case valueContent' cf of
    FunctionC f -> [toValue f]
    ExternalFunctionC ef -> [toValue ef]
    _ -> pointsTo pta cf

mapFirst :: (a -> Maybe b) -> [a] -> Maybe b
mapFirst f xs =
  case mapMaybe f xs of
    [] -> Nothing
    e : _ -> Just e
