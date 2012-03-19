{-# LANGUAGE TemplateHaskell #-}
module Foreign.Inference.Analysis.Escape (
  EscapeSummary,
  identifyEscapes,
  instructionEscapes
  ) where

import Control.DeepSeq
import Control.Monad.Writer
import Data.Lens.Common
import Data.Lens.Template

import LLVM.Analysis
import LLVM.Analysis.CallGraphSCCTraversal
import LLVM.Analysis.Escape hiding ( instructionEscapes )
import qualified LLVM.Analysis.Escape as LLVM

import Foreign.Inference.Diagnostics
import Foreign.Inference.Interface

data EscapeSummary =
  EscapeSummary { _escapeResult :: EscapeResult
                , _escapeDiagnostics :: Diagnostics
                }

$(makeLens ''EscapeSummary)

instance Eq EscapeSummary where
  (EscapeSummary s1 _) == (EscapeSummary s2 _) = s1 == s2

instance Monoid EscapeSummary where
  mempty = EscapeSummary mempty mempty
  mappend (EscapeSummary s1 d1) (EscapeSummary s2 d2) =
    EscapeSummary (s1 `mappend` s2) (d1 `mappend` d2)

instance NFData EscapeSummary where
  rnf e@(EscapeSummary s d) = s `deepseq` d `deepseq` e `seq` ()

instance HasDiagnostics EscapeSummary where
  diagnosticLens = escapeDiagnostics

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
  composableAnalysisM runner escapeWrapper lns
  where
    escapeWrapper f s = do
      er <- escapeAnalysis extSumm f (s ^. escapeResult)
      return $! (escapeResult ^= er) s

    runner a =
      let (e, diags) = runWriter a
      in (escapeDiagnostics ^= diags) e

    extSumm ef ix =
      case lookupArgumentSummary ds (undefined :: EscapeSummary) ef ix of
        Nothing -> do
          let msg = "Missing summary for " ++ show (externalFunctionName ef)
          emitWarning Nothing "EscapeAnalysis" msg
          return True
        Just annots -> return $ PAEscape `elem` annots

instructionEscapes :: EscapeSummary -> Instruction -> Bool
instructionEscapes (EscapeSummary er _) i =
  case LLVM.instructionEscapes er i of
    Nothing -> False
    Just _ -> True
