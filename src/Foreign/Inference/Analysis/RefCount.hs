{-# LANGUAGE TemplateHaskell, ViewPatterns #-}
{-|

1) Identify functions of 1 parameter that conditionally call a finalizer.

2) The condition should compare a value reachable from the argument
   against zero or one (record the access path)

3) Identify functions of one parameter incrementing something
   accessible via that same access path

-}
module Foreign.Inference.Analysis.RefCount where

import Control.DeepSeq
import Data.HashSet ( HashSet )
import qualified Data.HashSet as HS
import Data.Lens.Common
import Data.Lens.Template
import Data.Monoid

import LLVM.Analysis
import LLVM.Analysis.CFG
import LLVM.Analysis.CallGraphSCCTraversal

import Foreign.Inference.AnalysisMonad
import Foreign.Inference.Analysis.Finalize
import Foreign.Inference.Analysis.Util.AccessPath
import Foreign.Inference.Diagnostics
import Foreign.Inference.Interface

data RefCountSummary =
  RefCountSummary { _conditionalFinalizers :: HashSet Function
                  , _refCountDiagnostics :: !Diagnostics
                  }

$(makeLens ''RefCountSummary)

instance Monoid RefCountSummary where
  mempty = RefCountSummary mempty mempty
  mappend (RefCountSummary s1 d1) (RefCountSummary s2 d2) =
    RefCountSummary (s1 `mappend` s2) (d1 `mappend` d2)

instance NFData RefCountSummary where
  rnf r@(RefCountSummary s _) = s `deepseq` r `seq` ()

instance Eq RefCountSummary where
  (RefCountSummary s1 _) == (RefCountSummary s2 _) = s1 == s2

instance HasDiagnostics RefCountSummary where
  diagnosticLens = refCountDiagnostics
  -- addDiagnostics s d =
  --   s { refCountDiagnostics = refCountDiagnostics s `mappend` d }
  -- getDiagnostics = refCountDiagnostics

instance SummarizeModule RefCountSummary where
  summarizeFunction f (RefCountSummary s _) =
    case HS.member f s of
      True -> [FACondFinalizer]
      False -> []
  summarizeArgument _ _ = []

data RefCountData =
  RefCountData { dependencySummary :: DependencySummary
               }

type Analysis = AnalysisMonad RefCountData ()

identifyRefCounting :: (FuncLike funcLike, HasFunction funcLike, HasCFG funcLike)
                       => DependencySummary
                       -> Lens compositeSummary RefCountSummary
                       -> Lens compositeSummary FinalizerSummary
                       -> ComposableAnalysis compositeSummary funcLike
identifyRefCounting ds lns depLens =
  composableDependencyAnalysisM runner refCountAnalysis lns depLens
  where
    runner a = runAnalysis a constData ()
    constData = RefCountData ds

isConditionalFinalizer :: FinalizerSummary -> Function -> Analysis Bool
isConditionalFinalizer summ f =
  case functionIsFinalizer summ f of
    True -> return False
    False -> do
      ds <- asks dependencySummary
      return $! any (isFinalizerCall ds summ) functionInstructions
  where
    functionInstructions = concatMap basicBlockInstructions (functionBody f)

isFinalizerCall :: DependencySummary -> FinalizerSummary -> Instruction -> Bool
isFinalizerCall ds summ i =
  case i of
    CallInst { callFunction = (valueContent' -> FunctionC f) } ->
      functionIsFinalizer summ f
    CallInst { callFunction = (valueContent' -> ExternalFunctionC e) } ->
      externalIsFinalizer ds e
    InvokeInst { invokeFunction = (valueContent' -> FunctionC f) } ->
      functionIsFinalizer summ f
    InvokeInst { invokeFunction = (valueContent' -> ExternalFunctionC e) } ->
      externalIsFinalizer ds e
    _ -> False

externalIsFinalizer :: DependencySummary -> ExternalFunction -> Bool
externalIsFinalizer ds ef =
  any argFinalizes allArgAnnots
  where
    TypeFunction _ atypes _ = externalFunctionType ef
    maxArg = length atypes - 1
    allArgAnnots = map (lookupArgumentSummary ds ef) [0..maxArg]
    argFinalizes Nothing = False
    argFinalizes (Just annots) = any (==PAFinalize) annots

functionIsFinalizer :: FinalizerSummary -> Function -> Bool
functionIsFinalizer summ f = and (map snd annotatedArgs)
  where
    funcArgs = functionParameters f
    annotatedArgs = map (annotateArg summ) funcArgs

annotateArg :: FinalizerSummary -> Argument -> (Argument, Bool)
annotateArg summ a = (a, any doesFinalize (summarizeArgument a summ))
  where
    doesFinalize (PAFinalize, _) = True
    doesFinalize _ = False

refCountAnalysis :: (FuncLike funcLike, HasCFG funcLike, HasFunction funcLike)
                    => FinalizerSummary
                    -> funcLike
                    -> RefCountSummary
                    -> Analysis RefCountSummary
refCountAnalysis finSumm funcLike summ = do
  isCondFin <- isConditionalFinalizer finSumm f
  case isCondFin of
    False -> return summ
    True ->
      let newFin = HS.insert f (summ ^. conditionalFinalizers)
      in return $! (conditionalFinalizers ^= newFin) summ
  where
    f = getFunction funcLike