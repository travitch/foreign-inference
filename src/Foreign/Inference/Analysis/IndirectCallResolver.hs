{-# LANGUAGE ViewPatterns #-}
-- | FIXME: Currently there is an exception allowing us to identify
-- finalizers that are called through function pointers if the
-- function pointer is global and has an initializer.
--
-- This needs to be generalized to cover things that are initialized
-- once in the library code with a finalizer.  This will be a lower-level
-- analysis that answers the query:
--
-- > initializedOnce :: Value -> Maybe Value
--
-- where the returned value is the single initializer that was sourced
-- within the library.  This can be the current simple analysis for
-- globals with initializers.  Others will be analyzed in terms of
-- access paths (e.g., Field X of Type Y is initialized once with
-- value Z).
--
-- Linear scan for all stores, recording their access path.  Also look
-- at all globals (globals can be treated separately).  If an access
-- path gets more than one entry, stop tracking it.  Only record
-- stores where the value is some global entity.
--
-- Run this analysis after or before constructing the call graph and
-- initialize the whole-program summary with it.  It doesn't need to
-- be computed bottom up as part of the call graph traversal.
module Foreign.Inference.Analysis.IndirectCallResolver (
  IndirectCallSummary,
  identifyIndirectCallTargets,
  indirectCallInitializers,
  indirectCallTargets
  ) where

import Data.Map ( Map )
import qualified Data.Map as M
import Data.Maybe ( fromMaybe )
import Data.Monoid
import Data.Set ( Set )
import qualified Data.Set as S

import LLVM.Analysis
import LLVM.Analysis.ClassHierarchy
import LLVM.Analysis.PointsTo
import LLVM.Analysis.PointsTo.Andersen

-- import Text.Printf
-- import Debug.Trace
-- debug = flip trace

-- | This isn't a true points-to analysis because it is an
-- under-approximation.  However, that is sufficient for this library.
instance PointsToAnalysis IndirectCallSummary where
  mayAlias _ _ _ = True
  pointsTo = indirectCallInitializers
  resolveIndirectCall = indirectCallTargets

data IndirectCallSummary =
  ICS { summaryTargets :: Andersen
      , resolverCHA :: CHA
      , globalInits :: Map (Type, Int) (Set Value)
      }

-- If i is a Load of a global with an initializer (or a GEP of a
-- global with a complex initializer), just use the initializer to
-- determine the points-to set.  Obviously this isn't general.
--
-- Eventually, this should call down to a real (field-based) points-to
-- analysis for other values.
indirectCallInitializers :: IndirectCallSummary -> Value -> [Value]
indirectCallInitializers ics v =
  case valueContent' v of
    FunctionC f -> [toValue f]
    ExternalFunctionC ef -> [toValue ef]
    InstructionC li@LoadInst { loadAddress = (valueContent' ->
      InstructionC GetElementPtrInst { getElementPtrValue = base
                                     , getElementPtrIndices = [ (valueContent -> ConstantC ConstantInt { constantIntValue = 0 })
                                                              , (valueContent -> ConstantC ConstantInt { constantIntValue = (fromIntegral -> ix) })
                                                              ]
                                     })} -> fromMaybe (lookupInst li) $ do
      let baseTy = valueType base
      globInits <- M.lookup (baseTy, ix) (globalInits ics)
      return $ S.toList globInits ++ lookupInst li
    -- Here, walk the initializer if it isn't a simple integer
    -- constant We discard the first index because while the global
    -- variable is a pointer type, the initializer is not (because all
    -- globals get an extra indirection as r-values)
    InstructionC li@LoadInst { loadAddress = (valueContent' ->
      ConstantC ConstantValue { constantInstruction = (valueContent' ->
        InstructionC GetElementPtrInst { getElementPtrValue = (valueContent' ->
          GlobalVariableC GlobalVariable { globalVariableInitializer = Just i })
                                       , getElementPtrIndices = (valueContent -> ConstantC ConstantInt { constantIntValue = 0 }) :ixs
                                       })})} ->
      maybe (lookupInst li) (:[]) $ resolveInitializer i ixs
    InstructionC li@LoadInst { loadAddress = (valueContent' ->
      GlobalVariableC GlobalVariable { globalVariableInitializer = Just i })} ->
      case valueContent' i of
        -- All globals have some kind of initializer; if it is a zero
        -- or constant (non-function) initializer, just ignore it and
        -- use the more complex fallback.
        ConstantC _ -> lookupInst li
        _ -> [i]
    InstructionC li@LoadInst { } ->
      lookupInst li
    InstructionC i -> lookupInst i
    _ -> []
  where
    lookupInst i = pointsTo (summaryTargets ics) (toValue i)

resolveInitializer :: Value -> [Value] -> Maybe Value
resolveInitializer v [] = return (stripBitcasts v)
resolveInitializer v (ix:ixs) = do
  intVal <- fromConstantInt ix
  case valueContent v of
    ConstantC ConstantArray { constantArrayValues = vs } ->
      if length vs <= intVal then Nothing else resolveInitializer (vs !! intVal) ixs
    ConstantC ConstantStruct { constantStructValues = vs } ->
      if length vs <= intVal then Nothing else resolveInitializer (vs !! intVal) ixs
    _ -> Nothing

fromConstantInt :: Value -> Maybe Int
fromConstantInt v =
  case valueContent v of
    ConstantC ConstantInt { constantIntValue = iv } ->
      return $ fromIntegral iv
    _ -> Nothing

-- | Resolve the targets of an indirect call instruction.  This works
-- with both C++ virtual function dispatch and some other common
-- function pointer call patterns.  It is unsound and incomplete.
indirectCallTargets :: IndirectCallSummary -> Instruction -> [Value]
indirectCallTargets ics i =
  -- If this is a virtual function call (C++), use the virtual
  -- function resolver.  Otherwise, fall back to the normal function
  -- pointer analysis.
  maybe fptrTargets (fmap toValue) vfuncTargets
  where
    vfuncTargets = resolveVirtualCallee (resolverCHA ics) i
    fptrTargets =
      case i of
        CallInst { callFunction = f } ->
          indirectCallInitializers ics f
        InvokeInst { invokeFunction = f } ->
          indirectCallInitializers ics f
        _ -> []

-- | Run the initializer analysis: a cheap pass to identify a subset
-- of possible function pointers that object fields can point to.
identifyIndirectCallTargets :: Module -> IndirectCallSummary
identifyIndirectCallTargets m =
  ICS (runPointsToAnalysisWith ignoreNonFptr m) (runCHA m) gis
  where
    ignoreNonFptr = ignoreNonFptrType . valueType
    ignoreNonFptrType t =
      case t of
        TypeFunction _ _ _ -> False
        TypePointer t' _ -> ignoreNonFptrType t'
        _ -> True
    gis = foldr extractGlobalFieldInits mempty (moduleGlobalVariables m)

-- FIXME: One day push this hack down into the andersen analysis.
extractGlobalFieldInits :: GlobalVariable -> Map (Type, Int) (Set Value) -> Map (Type, Int) (Set Value)
extractGlobalFieldInits gv acc = fromMaybe acc $ do
  ConstantC ConstantStruct { constantStructValues = vs } <- globalVariableInitializer gv
  return $ foldr (addFieldInit (valueType gv)) acc (zip [0..] vs)
  where
    addFieldInit t (ix, v) =
      M.insertWith S.union (t, ix) (S.singleton v)

-- Find all initializers of function types to global fields.  Make a map
-- of (struct type, field no) -> {initializers}