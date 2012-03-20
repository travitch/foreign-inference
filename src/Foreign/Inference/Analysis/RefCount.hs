{-# LANGUAGE TemplateHaskell, ViewPatterns #-}
{-|

1) Identify functions of 1 parameter that conditionally call a finalizer.

2) The condition should compare a value reachable from the argument
   against zero or one (record the access path)

3) Identify functions of one parameter incrementing something
   accessible via that same access path

-}
module Foreign.Inference.Analysis.RefCount (
  RefCountSummary,
  identifyRefCounting
  ) where

import Control.Arrow
import Control.DeepSeq
import Data.HashSet ( HashSet )
import qualified Data.HashSet as HS
import Data.Lens.Common
import Data.Lens.Template
import Data.Maybe ( mapMaybe )
import Data.Monoid
import Debug.Trace.LocationTH

import LLVM.Analysis
import LLVM.Analysis.AccessPath
import LLVM.Analysis.CFG
import LLVM.Analysis.CallGraphSCCTraversal

import Foreign.Inference.AnalysisMonad
import Foreign.Inference.Analysis.Finalize
import Foreign.Inference.Analysis.ScalarEffects
import Foreign.Inference.Diagnostics
import Foreign.Inference.Interface

import Text.Printf
import Debug.Trace
debug = flip trace

data RefCountSummary =
  RefCountSummary { _conditionalFinalizers :: HashSet Function
                  , _unrefArguments :: HashSet Argument
                  , _refCountDiagnostics :: !Diagnostics
                  }

$(makeLens ''RefCountSummary)

instance Monoid RefCountSummary where
  mempty = RefCountSummary mempty mempty mempty
  mappend (RefCountSummary s1 a1 d1) (RefCountSummary s2 a2 d2) =
    RefCountSummary (s1 `mappend` s2) (a1 `mappend` a2) (d1 `mappend` d2)

instance NFData RefCountSummary where
  rnf r@(RefCountSummary s a _) = s `deepseq` a `deepseq` r `seq` ()

instance Eq RefCountSummary where
  (RefCountSummary s1 a1 _) == (RefCountSummary s2 a2 _) =
    s1 == s2 && a1 == a2

instance HasDiagnostics RefCountSummary where
  diagnosticLens = refCountDiagnostics

instance SummarizeModule RefCountSummary where
  summarizeFunction f (RefCountSummary s _ _) =
    case HS.member f s of
      True -> [FACondFinalizer]
      False -> []
  summarizeArgument a (RefCountSummary _ am _) =
    case HS.member a am of
      False -> []
      True -> [(PAUnref, [])]

data RefCountData =
  RefCountData { dependencySummary :: DependencySummary
               }

type Analysis = AnalysisMonad RefCountData ()

identifyRefCounting :: (FuncLike funcLike, HasFunction funcLike, HasCFG funcLike)
                       => DependencySummary
                       -> Lens compositeSummary RefCountSummary
                       -> Lens compositeSummary FinalizerSummary
                       -> Lens compositeSummary ScalarEffectSummary
                       -> ComposableAnalysis compositeSummary funcLike
identifyRefCounting ds lns depLens1 depLens2 =
  composableDependencyAnalysisM runner refCountAnalysis lns depLens
  where
    runner a = runAnalysis a constData ()
    constData = RefCountData ds
    depLens = lens (getL depLens1 &&& getL depLens2) (\(f, s) -> setL depLens1 f . setL depLens2 s)

isConditionalFinalizer :: FinalizerSummary -> Function -> [Instruction] -> Analysis Bool
isConditionalFinalizer summ f funcInstructions = do
  ds <- asks dependencySummary
  case functionIsFinalizer ds summ (Value f) of
    True -> return False
    False -> return $! any (isFinalizerCall ds summ) funcInstructions

isFinalizerCall :: DependencySummary -> FinalizerSummary -> Instruction -> Bool
isFinalizerCall ds summ i =
  case i of
    CallInst { callFunction = callee } ->
      functionIsFinalizer ds summ callee
    InvokeInst { invokeFunction = callee } ->
      functionIsFinalizer ds summ callee
    _ -> False

functionIsFinalizer :: DependencySummary -> FinalizerSummary -> Value -> Bool
functionIsFinalizer ds fs callee =
  any argFinalizes allArgAnnots
  where
    atypes = case valueType callee of
      TypeFunction _ ats _ -> ats
      TypePointer (TypeFunction _ ats _) _ -> ats
      _ -> $failure ("Expected function type: " ++ show (valueType callee))
    maxArg = length atypes - 1
    allArgAnnots = map (lookupArgumentSummary ds fs callee) [0..maxArg]
    argFinalizes Nothing = False
    argFinalizes (Just annots) = PAFinalize `elem` annots

annotateArg :: FinalizerSummary -> Argument -> (Argument, Bool)
annotateArg summ a = (a, any doesFinalize (summarizeArgument a summ))
  where
    doesFinalize (PAFinalize, _) = True
    doesFinalize _ = False

refCountAnalysis :: (FuncLike funcLike, HasCFG funcLike, HasFunction funcLike)
                    => (FinalizerSummary, ScalarEffectSummary)
                    -> funcLike
                    -> RefCountSummary
                    -> Analysis RefCountSummary
refCountAnalysis (finSumm, seSumm) funcLike summ = do
  isCondFin <- isConditionalFinalizer finSumm f functionInstructions
  case isCondFin of
    False -> return summ
    True ->
      let newFin = HS.insert f (summ ^. conditionalFinalizers)
          -- If this is a conditional finalizer, figure out which
          -- field (if any) is unrefed.
          newUnref = case (refCountFields seSumm f, functionParameters f) of
            ([_], [a]) -> HS.insert a (summ ^. unrefArguments)
            _ -> summ ^. unrefArguments
      in return $! (unrefArguments ^= newUnref) $ (conditionalFinalizers ^= newFin) summ -- `debug`
           -- printf "%s calls through fptr: %s\n" (show (functionName f)) (show fptrAccessPaths)
         -- `debug`
         --   printf "Ref counted fields: %s\n" (show (refCountFields seSumm f))
  where
    f = getFunction funcLike
    functionInstructions = concatMap basicBlockInstructions (functionBody f)
    fptrAccessPaths = mapMaybe indirectCallAccessPath functionInstructions

indirectCallAccessPath :: Instruction -> Maybe AccessPath
indirectCallAccessPath i =
  case i of
    CallInst { callFunction = f } -> notDirect f
    InvokeInst { invokeFunction = f } -> notDirect f
    _ -> Nothing
  where
    notDirect v =
      case valueContent' v of
        FunctionC _ -> Nothing
        ExternalFunctionC _ -> Nothing
        InstructionC callee -> accessPath callee
        _ -> Nothing


-- If we find a ref counting function that calls some functions
-- through a function pointer of one argument (where that argument is
-- reachable from the argument of the current function), try to
-- resolve the function pointer using the initializer value analysis.
--
-- Check what each of those possible call targets casts their argument
-- to.

-- For incRef, look for scalar effects of Add1 for access paths
-- matching the decRef access path.  We can look at functions that
-- have already been processed by the scalar effects pass.  That isn't
-- enough, though, because the function might not have been analyzed yet.
-- So check:
--
--  (1) after identifying an unref function, and
--
--  (2) before analyzing a function (check a list of un-identified
--      increfs)
--

refCountFields :: ScalarEffectSummary -> Function -> [AbstractAccessPath]
refCountFields seSumm f = mapMaybe (checkRefCount seSumm args) allInsts
  where
    args = HS.fromList $ functionParameters f
    allInsts = concatMap basicBlockInstructions (functionBody f)

-- FIXME: Add support for cmpxchg?
checkRefCount :: ScalarEffectSummary
                 -> HashSet Argument
                 -> Instruction
                 -> Maybe AbstractAccessPath
checkRefCount seSumm args i =
  case i of
    AtomicRMWInst { atomicRMWOperation = AOSub
                  , atomicRMWValue = (valueContent ->
      ConstantC ConstantInt { constantIntValue = 1 })} ->
      absPathIfArg args i
    AtomicRMWInst { atomicRMWOperation = AOAdd
                  , atomicRMWValue =
      (valueContent -> ConstantC ConstantInt { constantIntValue = -1 })} ->
      absPathIfArg args i
    StoreInst { storeValue = (valueContent' ->
      InstructionC SubInst { binaryRhs = (valueContent' ->
        ConstantC ConstantInt { constantIntValue = 1 })
                           , binaryLhs = (valueContent' ->
        InstructionC oldRefCount) })} ->
      absPathIfArg args oldRefCount
    StoreInst { storeValue = (valueContent' ->
      InstructionC AddInst { binaryRhs = (valueContent' ->
        ConstantC ConstantInt { constantIntValue = -1 })
                           , binaryLhs = (valueContent' ->
        InstructionC oldRefCount) })} ->
      absPathIfArg args oldRefCount
    StoreInst { storeValue = (valueContent' ->
      InstructionC AddInst { binaryLhs = (valueContent' ->
        ConstantC ConstantInt { constantIntValue = -1 })
                           , binaryRhs = (valueContent' ->
        InstructionC oldRefCount) })} ->
      absPathIfArg args oldRefCount
    CallInst { callFunction = (valueContent' -> FunctionC f)
             , callArguments = [(a,_)]
             } ->
      absPathThroughCall seSumm args (functionParameters f) a
    InvokeInst { invokeFunction = (valueContent' -> FunctionC f)
               , invokeArguments = [(a,_)]
               } ->
      absPathThroughCall seSumm args (functionParameters f) a
    _ -> Nothing

absPathThroughCall :: ScalarEffectSummary
                      -> HashSet Argument
                      -> [Argument]
                      -> Value
                      -> Maybe AbstractAccessPath
absPathThroughCall seSumm args [singleFormal] actual = do
  -- This is the access path of the argument of the callee (if and
  -- only if the function subtracts one from an int component of the
  -- argument).  The access path describes *which* component of the
  -- argument is modified.
  calleeAccessPath <- scalarEffectSubOne seSumm singleFormal
  case valueContent' actual of
    InstructionC i -> do
      actualAccessPath <- accessPath i
      -- Now see if the actual passed to this call is derived from one
      -- of the formal parameters of the current function.  This
      -- access path tells us which component of the argument was
      -- passed to the callee.
      return () `debug` printf "Callee: %s\nCaller: %s\n" (show calleeAccessPath) (show actualAccessPath)
      case valueContent' (accessPathBaseValue actualAccessPath) of
        ArgumentC baseArg ->
          case baseArg `HS.member` args of
            -- If it really was derived from an argument, connect up
            -- the access paths for the caller and callee so we have a
            -- single description of the field that was modified
            -- (interprocedurally).
            True -> abstractAccessPath actualAccessPath `appendAccessPath` calleeAccessPath
            False -> Nothing
        _ -> Nothing
    _ -> Nothing
absPathThroughCall _ _ _ _ = Nothing

absPathIfArg :: HashSet Argument -> Instruction -> Maybe AbstractAccessPath
absPathIfArg args i =
  case accessPath i of
    Nothing -> Nothing
    Just cap ->
      case valueContent' (accessPathBaseValue cap) of
        ArgumentC a ->
          case HS.member a args of
            False -> Nothing
            True -> Just (abstractAccessPath cap)
        _ -> Nothing