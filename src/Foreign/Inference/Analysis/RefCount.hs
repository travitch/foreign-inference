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
  identifyRefCounting,
  -- * Testing
  refCountSummaryToTestFormat
  ) where

import Control.Arrow
import Control.DeepSeq
import Data.HashSet ( HashSet )
import qualified Data.HashSet as HS
import Data.HashMap.Strict ( HashMap )
import qualified Data.HashMap.Strict as HM
import Data.Lens.Common
import Data.Lens.Template
import Data.List ( find )
import Data.Map ( Map )
import qualified Data.Map as M
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

-- import Text.Printf
-- import Debug.Trace
-- debug = flip trace

data RefCountSummary =
  RefCountSummary { _conditionalFinalizers :: HashSet Function
                  , _unrefArguments :: HashMap Argument (AbstractAccessPath, [Witness])
                  , _refArguments :: HashMap Argument (AbstractAccessPath, [Witness])
                  , _refCountDiagnostics :: !Diagnostics
                  }

$(makeLens ''RefCountSummary)

instance Monoid RefCountSummary where
  mempty = RefCountSummary mempty mempty mempty mempty
  mappend (RefCountSummary s1 a1 r1 d1) (RefCountSummary s2 a2 r2 d2) =
    RefCountSummary (s1 `mappend` s2) (a1 `mappend` a2) (r1 `mappend` r2) (d1 `mappend` d2)

instance NFData RefCountSummary where
  rnf r@(RefCountSummary s a rr _) = s `deepseq` a `deepseq` rr `deepseq` r `seq` ()

instance Eq RefCountSummary where
  (RefCountSummary s1 a1 r1 _) == (RefCountSummary s2 a2 r2 _) =
    s1 == s2 && a1 == a2 && r1 == r2

instance HasDiagnostics RefCountSummary where
  diagnosticLens = refCountDiagnostics

-- | The summarizing functions match incref and decref functions.  We
-- need to do that here rather than on the fly since either could be
-- analyzed before the other, so every analysis step would have to try
-- to match up any outstanding references.  Here we can just do it on
-- demand.
--
-- Matching is done based on argument type and the access path used to
-- modify the reference count parameter.  If an unref function matches
-- up with exactly one ref function, they are paired by name.  The
-- code generator should deal with it appropriately.
instance SummarizeModule RefCountSummary where
  -- FIXME: Eventually remove FACondFinalizer from the output.  It
  -- isn't useful for code generators (though it is nice for
  -- debugging)
  summarizeFunction f (RefCountSummary s _ _ _) =
    case HS.member f s of
      True -> [FACondFinalizer]
      False -> []
  summarizeArgument a (RefCountSummary _ unrefArgs refArgs _) =
    case HM.lookup a unrefArgs of
      Nothing ->
        case HM.lookup a refArgs of
          Nothing -> []
          Just (fieldPath, ws) ->
            case matchingTypeAndPath (argumentType a) fieldPath unrefArgs of
              Nothing -> [(PAAddRef "", ws)]
              Just fname -> [(PAAddRef fname, ws)]
      Just (fieldPath, ws) ->
        case matchingTypeAndPath (argumentType a) fieldPath refArgs of
          Nothing -> [(PAUnref "", ws)]
          Just fname -> [(PAUnref fname, ws)]

matchingTypeAndPath :: Type
                       -> AbstractAccessPath
                       -> HashMap Argument (AbstractAccessPath, [Witness])
                       -> Maybe String
matchingTypeAndPath t accPath m =
  case filter matchingPair pairs of
    [(singleMatch, _)] ->
      let f = argumentFunction singleMatch
      in Just $ identifierAsString (functionName f)
    _ -> Nothing
  where
    pairs = HM.toList m
    matchingPair (arg, (path, _)) = argumentType arg == t && path == accPath


data RefCountData =
  RefCountData { dependencySummary :: DependencySummary
               }

type Analysis = AnalysisMonad RefCountData ()

-- | The main analysis to identify both incref and decref functions.
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

isConditionalFinalizer :: FinalizerSummary -> Function -> [Instruction] -> Analysis (Maybe Instruction)
isConditionalFinalizer summ f funcInstructions = do
  ds <- asks dependencySummary
  case functionIsFinalizer ds summ (Value f) of
    True -> return Nothing
    False -> return $! find (isFinalizerCall ds summ) funcInstructions

isFinalizerCall :: DependencySummary -> FinalizerSummary -> Instruction -> Bool
isFinalizerCall ds summ i =
  case i of
    CallInst { callFunction = callee, callArguments = args } ->
      functionIsFinalizer ds summ callee && any isArgument (map fst args)
    InvokeInst { invokeFunction = callee, invokeArguments = args } ->
      functionIsFinalizer ds summ callee && any isArgument (map fst args)
    _ -> False

isArgument :: Value -> Bool
isArgument v =
  case valueContent' v of
    ArgumentC _ -> True
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
  let summ' = incRefAnalysis seSumm f summ
  condFinInstruction <- isConditionalFinalizer finSumm f functionInstructions
  case condFinInstruction of
    Nothing -> return summ'
    Just cfi ->
      let newFin = HS.insert f (summ' ^. conditionalFinalizers)
          finWitness = Witness cfi "condfin"
          curUnref = summ' ^. unrefArguments
          -- If this is a conditional finalizer, figure out which
          -- field (if any) is unrefed.
          newUnref = case (decRefCountFields seSumm f, functionParameters f) of
            ([(accPath, decWitness)], [a]) ->
              HM.insert a (accPath, [finWitness, decWitness]) curUnref
            _ -> curUnref
      in return $! (unrefArguments ^= newUnref) $ (conditionalFinalizers ^= newFin) summ' -- `debug`
  where
    f = getFunction funcLike
    functionInstructions = concatMap basicBlockInstructions (functionBody f)
    fptrAccessPaths = mapMaybe indirectCallAccessPath functionInstructions

incRefAnalysis :: ScalarEffectSummary -> Function -> RefCountSummary -> RefCountSummary
incRefAnalysis seSumm f summ =
  case (incRefCountFields seSumm f, functionParameters f) of
    ([], _) -> summ
    ([(fieldPath, w)], [a]) ->
      let newAddRef = HM.insert a (fieldPath, [w]) (summ ^. refArguments)
      in (refArguments ^= newAddRef) summ
    _ -> summ

-- | If the instruction is an indirect function call, return the
-- *concrete* AccessPath from which the function pointer was obtained.
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

-- | Find all of the fields of argument objects that are decremented
-- in the given Function, returning the affected AbstractAccessPaths
decRefCountFields :: ScalarEffectSummary -> Function -> [(AbstractAccessPath, Witness)]
decRefCountFields seSumm f = mapMaybe (checkDecRefCount seSumm) allInsts
  where
    allInsts = concatMap basicBlockInstructions (functionBody f)

-- | Likewise, but for incremented fields
incRefCountFields :: ScalarEffectSummary -> Function -> [(AbstractAccessPath, Witness)]
incRefCountFields seSumm f = mapMaybe (checkIncRefCount seSumm) allInsts
  where
    allInsts = concatMap basicBlockInstructions (functionBody f)

-- | This function checks whether or not the given 'Instruction'
-- decrements a reference count (really, any integer field embedded in
-- an object).  If it does, the function returns the
-- AbstractAccessPath that was decremented.
--
-- FIXME: Add support for cmpxchg?
checkDecRefCount :: ScalarEffectSummary
                    -> Instruction
                    -> Maybe (AbstractAccessPath, Witness)
checkDecRefCount seSumm i = do
  p <- case i of
    AtomicRMWInst { atomicRMWOperation = AOSub
                  , atomicRMWValue = (valueContent ->
      ConstantC ConstantInt { constantIntValue = 1 })} ->
      absPathIfArg i
    AtomicRMWInst { atomicRMWOperation = AOAdd
                  , atomicRMWValue =
      (valueContent -> ConstantC ConstantInt { constantIntValue = -1 })} ->
      absPathIfArg i
    StoreInst { storeValue = (valueContent' ->
      InstructionC SubInst { binaryRhs = (valueContent' ->
        ConstantC ConstantInt { constantIntValue = 1 })
                           , binaryLhs = (valueContent' ->
        InstructionC oldRefCount) })} ->
      absPathIfArg oldRefCount
    StoreInst { storeValue = (valueContent' ->
      InstructionC AddInst { binaryRhs = (valueContent' ->
        ConstantC ConstantInt { constantIntValue = -1 })
                           , binaryLhs = (valueContent' ->
        InstructionC oldRefCount) })} ->
      absPathIfArg oldRefCount
    StoreInst { storeValue = (valueContent' ->
      InstructionC AddInst { binaryLhs = (valueContent' ->
        ConstantC ConstantInt { constantIntValue = -1 })
                           , binaryRhs = (valueContent' ->
        InstructionC oldRefCount) })} ->
      absPathIfArg oldRefCount
    CallInst { callFunction = (valueContent' -> FunctionC f)
             , callArguments = [(a,_)]
             } ->
      absPathThroughCall seSumm scalarEffectSubOne (functionParameters f) a
    InvokeInst { invokeFunction = (valueContent' -> FunctionC f)
               , invokeArguments = [(a,_)]
               } ->
      absPathThroughCall seSumm scalarEffectSubOne (functionParameters f) a
    _ -> Nothing
  return (p, Witness i "decr")

-- | Analogous to 'checkDecRefCount', but for increments
checkIncRefCount :: ScalarEffectSummary
                    -> Instruction
                    -> Maybe (AbstractAccessPath, Witness)
checkIncRefCount seSumm i = do
  p <- case i of
    AtomicRMWInst { atomicRMWOperation = AOAdd
                  , atomicRMWValue = (valueContent ->
      ConstantC ConstantInt { constantIntValue = 1 })} ->
      absPathIfArg i
    AtomicRMWInst { atomicRMWOperation = AOSub
                  , atomicRMWValue =
      (valueContent -> ConstantC ConstantInt { constantIntValue = -1 })} ->
      absPathIfArg i
    StoreInst { storeValue = (valueContent' ->
      InstructionC SubInst { binaryRhs = (valueContent' ->
        ConstantC ConstantInt { constantIntValue = -1 })
                           , binaryLhs = (valueContent' ->
        InstructionC oldRefCount) })} ->
      absPathIfArg oldRefCount
    StoreInst { storeValue = (valueContent' ->
      InstructionC AddInst { binaryRhs = (valueContent' ->
        ConstantC ConstantInt { constantIntValue = 1 })
                           , binaryLhs = (valueContent' ->
        InstructionC oldRefCount) })} ->
      absPathIfArg oldRefCount
    StoreInst { storeValue = (valueContent' ->
      InstructionC AddInst { binaryLhs = (valueContent' ->
        ConstantC ConstantInt { constantIntValue = 1 })
                           , binaryRhs = (valueContent' ->
        InstructionC oldRefCount) })} ->
      absPathIfArg oldRefCount
    CallInst { callFunction = (valueContent' -> FunctionC f)
             , callArguments = [(a,_)]
             } ->
      absPathThroughCall seSumm scalarEffectAddOne (functionParameters f) a
    InvokeInst { invokeFunction = (valueContent' -> FunctionC f)
               , invokeArguments = [(a,_)]
               } ->
      absPathThroughCall seSumm scalarEffectAddOne (functionParameters f) a
    _ -> Nothing
  return (p, Witness i "incr")

-- | At a call site, if the callee has a scalar effect on its argument,
-- match up the access path of the actual argument passed to the callee
-- with the access path affected by the callee.
--
-- The scalar effect desired is controlled by the second argument and
-- should probably be one of
--
--  * scalarEffectAddOne
--
--  * scalarEffectSubOne
--
-- This function is meant to determine the effective abstract access
-- path of increments/decrements performed by called functions on data
-- in the caller.  For example:
--
-- > void decRef(Object * o) {
-- >   atomic_dec(&o->refCount);
-- > }
--
-- In this example, @atomic_dec@ only decrements the location passed
-- to it.  The abstract access path of the call instruction, however,
-- (and the value returned by this function) is Object/refCount.
--
-- This function deals only with single-argument callees
absPathThroughCall :: ScalarEffectSummary
                      -> (ScalarEffectSummary -> Argument -> Maybe AbstractAccessPath) -- ^ Type of access
                      -> [Argument] -- ^ Argument list of the callee
                      -> Value -- ^ Actual argument at call site
                      -> Maybe AbstractAccessPath
absPathThroughCall seSumm effect [singleFormal] actual = do
  -- This is the access path of the argument of the callee (if and
  -- only if the function subtracts one from an int component of the
  -- argument).  The access path describes *which* component of the
  -- argument is modified.
  calleeAccessPath <- effect seSumm singleFormal
  case valueContent' actual of
    InstructionC i -> do
      actualAccessPath <- accessPath i
      -- Now see if the actual passed to this call is derived from one
      -- of the formal parameters of the current function.  This
      -- access path tells us which component of the argument was
      -- passed to the callee.
      case valueContent' (accessPathBaseValue actualAccessPath) of
        -- If it really was derived from an argument, connect up
        -- the access paths for the caller and callee so we have a
        -- single description of the field that was modified
        -- (interprocedurally).
        ArgumentC _ ->
          abstractAccessPath actualAccessPath `appendAccessPath` calleeAccessPath
        _ -> Nothing
    _ -> Nothing
absPathThroughCall _ _ _ _ = Nothing

-- | If the Instruction produces an access path rooted at an Argument,
-- return the corresponding AbstractAccessPath
absPathIfArg :: Instruction -> Maybe AbstractAccessPath
absPathIfArg i =
  case accessPath i of
    Nothing -> Nothing
    Just cap ->
      case valueContent' (accessPathBaseValue cap) of
        ArgumentC _ -> Just (abstractAccessPath cap)
        _ -> Nothing

-- Testing

-- | Extract a map of unref functions to ref functions
refCountSummaryToTestFormat :: RefCountSummary -> Map String String
refCountSummaryToTestFormat (RefCountSummary _ unrefArgs refArgs _) =
  foldr addIfRefFound mempty (HM.toList unrefArgs)
  where
    addIfRefFound (uarg, (fieldPath, _)) acc =
      let ufunc = identifierAsString $ functionName $ argumentFunction uarg
      in case matchingTypeAndPath (argumentType uarg) fieldPath refArgs of
        Nothing -> acc
        Just rfunc -> M.insert ufunc rfunc acc
