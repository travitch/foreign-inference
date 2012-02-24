module Foreign.Inference.Analysis.Escape (
  EscapeSummary,
  identifyEscapes,
  instructionEscapes
  ) where

import Control.Monad.Writer

import Data.LLVM
import Data.LLVM.Analysis.CallGraph
import Data.LLVM.Analysis.Escape hiding ( instructionEscapes )
import qualified Data.LLVM.Analysis.Escape as LLVM

import Foreign.Inference.Diagnostics
import Foreign.Inference.Interface

newtype EscapeSummary = ES EscapeResult

instance SummarizeModule EscapeSummary where
  summarizeFunction _ _ = []
  summarizeArgument = summarizeEscapeArgument

summarizeEscapeArgument :: Argument -> EscapeSummary -> [(ParamAnnotation, [Witness])]
summarizeEscapeArgument a (ES er) =
  case argumentEscapes er a of
    Nothing -> []
    Just w@RetInst {} -> [(PAWillEscape, [Witness w "ret"])]
    Just w@CallInst {} -> [(PAEscape, [Witness w "call"])]
    Just w -> [(PAEscape, [Witness w "store"])]

identifyEscapes :: DependencySummary -> CallGraph -> (EscapeSummary, Diagnostics)
identifyEscapes ds cg = (ES er, diags)
  where
    (er, diags) = runWriter analysis
    analysis = escapeAnalysis cg extSumm
    extSumm ef ix =
      case lookupArgumentSummary ds ef ix of
        Nothing -> do
          let msg = "Missing summary for " ++ show (externalFunctionName ef)
          emitWarning Nothing "EscapeAnalysis" msg
          return True
        Just annots -> return $ PAEscape `elem` annots

instructionEscapes :: EscapeSummary -> Instruction -> Bool
instructionEscapes (ES er) i =
  case LLVM.instructionEscapes er i of
    Nothing -> False
    Just _ -> True
