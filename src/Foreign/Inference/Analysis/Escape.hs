module Foreign.Inference.Analysis.Escape (
  EscapeSummary,
  identifyEscapes,
  instructionEscapes
  ) where

import Control.DeepSeq
import Control.Monad.Writer
import Data.Lens.Common

import Data.LLVM
import Data.LLVM.Analysis.CallGraphSCCTraversal
import Data.LLVM.Analysis.Escape hiding ( instructionEscapes )
import qualified Data.LLVM.Analysis.Escape as LLVM

import Foreign.Inference.AnalysisMonad
import Foreign.Inference.Diagnostics
import Foreign.Inference.Interface

data EscapeSummary =
  EscapeSummary { escapeResult :: EscapeResult
                , escapeDiagnostics :: Diagnostics
                }

instance Eq EscapeSummary where
  (EscapeSummary s1 _) == (EscapeSummary s2 _) = s1 == s2

instance Monoid EscapeSummary where
  mempty = EscapeSummary mempty mempty
  mappend (EscapeSummary s1 d1) (EscapeSummary s2 d2) =
    EscapeSummary (s1 `mappend` s2) (d1 `mappend` d2)

instance NFData EscapeSummary where
  rnf e@(EscapeSummary s d) = s `deepseq` d `deepseq` e `seq` ()

instance HasDiagnostics EscapeSummary where
  addDiagnostics s d =
    s { escapeDiagnostics = escapeDiagnostics s `mappend` d }
  getDiagnostics = escapeDiagnostics

instance SummarizeModule EscapeSummary where
  summarizeFunction _ _ = []
  summarizeArgument = summarizeEscapeArgument

summarizeEscapeArgument :: Argument -> EscapeSummary -> [(ParamAnnotation, [Witness])]
summarizeEscapeArgument a (EscapeSummary er _) =
  case argumentEscapes er a of
    Nothing -> []
    Just w@RetInst {} -> [(PAWillEscape, [Witness w "ret"])]
    Just w@CallInst {} -> [(PAEscape, [Witness w "call"])]
    Just w -> [(PAEscape, [Witness w "store"])]

identifyEscapes :: (FuncLike funcLike, HasFunction funcLike)
                   => DependencySummary
                   -> Lens compositeSummary EscapeSummary
                   -> ComposableAnalysis compositeSummary funcLike
identifyEscapes ds lns =
  monadicComposableAnalysis runner escapeWrapper lns
  where
    escapeWrapper f s = do
      er <- escapeAnalysis extSumm f (escapeResult s)
      return $! s { escapeResult = er }

    runner a =
      let (e, diags) = runWriter a
      in e { escapeDiagnostics = diags }

    extSumm ef ix =
      case lookupArgumentSummary ds ef ix of
        Nothing -> do
          let msg = "Missing summary for " ++ show (externalFunctionName ef)
          emitWarning Nothing "EscapeAnalysis" msg
          return True
        Just annots -> return $ PAEscape `elem` annots

{-
identifyEscapes :: DependencySummary -> CallGraph -> EscapeSummary
identifyEscapes ds cg =
  -- parallelCallGraphSCCTraversal cg runner escapeWrapper mempty
  parallelCallGraphSCCTraversal cg analysisFunction mempty
  where
    analysisFunction = callGraphAnalysisM runner escapeWrapper
    escapeWrapper f s = do
      er <- escapeAnalysis extSumm f (escapeResult s)
      return $! s { escapeResult = er }
    runner a =
      let (e, diags) = runWriter a
      in e { escapeDiagnostics = diags }

    extSumm ef ix =
      case lookupArgumentSummary ds ef ix of
        Nothing -> do
          let msg = "Missing summary for " ++ show (externalFunctionName ef)
          emitWarning Nothing "EscapeAnalysis" msg
          return True
        Just annots -> return $ PAEscape `elem` annots
-}

instructionEscapes :: EscapeSummary -> Instruction -> Bool
instructionEscapes (EscapeSummary er _) i =
  case LLVM.instructionEscapes er i of
    Nothing -> False
    Just _ -> True
