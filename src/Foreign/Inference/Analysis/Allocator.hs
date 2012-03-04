{-# LANGUAGE ViewPatterns #-}
{-|

This analysis identifies functions that are allocators (in the style
of malloc).

An function @f@ is an allocator if it always returns the result of an
allocator or NULL, but must be able to return non-NULL.  Additionally,
none of the returned allocations may *escape* the function.  See the
escape analysis for a precise definition of escaping.

The initial set of allocators is derived from the C standard library
(malloc, calloc).  Support for C++ new allocations will be added.

As a special exception, an allocator may allocate a chunk of memory
using another allocator and then return a pointer to some location
inside of the chunk to the user.  Example:

> void *glp_malloc(int size) {
>   void* ret = malloc(size + 10);
>   return (void*)((char*)ret + 10);
> }

This facilitates allocators that allocate object headers to store
metadata that they do not wish to expose to the user.

-}
module Foreign.Inference.Analysis.Allocator (
  AllocatorSummary,
  identifyAllocators,
  -- * Testing
  allocatorSummaryToTestFormat
  ) where

import Control.DeepSeq
import Data.Map ( Map )
import qualified Data.Map as M

import Data.LLVM
import Data.LLVM.Analysis.CallGraphSCCTraversal

import Foreign.Inference.AnalysisMonad
import Foreign.Inference.Diagnostics
import Foreign.Inference.Interface
import Foreign.Inference.Analysis.Escape
-- import Foreign.Inference.Analysis.Finalize
import Foreign.Inference.Internal.FlattenValue

-- import Debug.Trace
-- debug = flip trace

type SummaryType = Map Function (Maybe String)
data AllocatorSummary =
  AllocatorSummary { allocatorSummary :: SummaryType
                   , allocatorDiagnostics :: Diagnostics
                   }

instance Eq AllocatorSummary where
  (AllocatorSummary s1 _) == (AllocatorSummary s2 _) = s1 == s2

instance Monoid AllocatorSummary where
  mempty = AllocatorSummary mempty mempty
  mappend (AllocatorSummary s1 d1) (AllocatorSummary s2 d2) =
    AllocatorSummary (M.unionWith merge s1 s2) (mappend d1 d2)
    where
      merge Nothing Nothing = Nothing
      merge v@(Just _) _ = v
      merge _ v = v

instance NFData AllocatorSummary where
  rnf a@(AllocatorSummary s d) = s `deepseq` d `deepseq` a `seq` ()

instance HasDiagnostics AllocatorSummary where
  addDiagnostics s d =
    s { allocatorDiagnostics = allocatorDiagnostics s `mappend` d }
  getDiagnostics = allocatorDiagnostics

data AllocatorData =
  AllocatorData { dependencySummary :: DependencySummary
                }

type Analysis = AnalysisMonad AllocatorData ()

instance SummarizeModule AllocatorSummary where
  summarizeArgument _ _ = []
  summarizeFunction f (AllocatorSummary summ _) =
    case M.lookup f summ of
      Nothing -> []
      Just (Just fin) -> [FAAllocator fin]
      Just Nothing -> [FAAllocator ""]

identifyAllocators :: (FuncLike funcLike, HasFunction funcLike)
                      => DependencySummary
                      -> Lens compositeSummary AllocatorSummary
                      -> Lens compositeSummary EscapeSummary
                      -> ComposableAnalysis compositeSummary funcLike
identifyAllocators ds lns depLens =
  composableDependencyAnalysisM runner allocatorAnalysis lns depLens
  where
    runner a = runAnalysis a readOnlyData ()
    readOnlyData = AllocatorData ds

-- | If the function returns a pointer, it is a candidate for an
-- allocator.  We do not concern ourselves with functions that may
-- unwind or call exit on error - these can also be allocators.
allocatorAnalysis :: (FuncLike funcLike, HasFunction funcLike)
                     => EscapeSummary
                     -> funcLike
                     -> AllocatorSummary
                     -> Analysis AllocatorSummary
allocatorAnalysis esumm funcLike s@(AllocatorSummary summ _) =
  case exitInst of
    RetInst { retInstValue = Just rv } ->
      case valueType rv of
        -- The function always returns a pointer
        TypePointer _ _ -> do
          summ' <- checkReturn esumm f rv summ
          return s { allocatorSummary = summ' }
        -- Non-pointer return, ignore
        _ -> return s
    -- Returns void
    _ -> return s
  where
    f = getFunction funcLike
    exitInst = functionExitInstruction f

-- | If the return value is always one of:
--
--  * NULL
--
--  * The result of an allocator (and does not escape)
--
-- then f is an allocator.  If there is a unique finalizer for the
-- same type, associate it with this allocator.
checkReturn :: EscapeSummary -> Function -> Value -> SummaryType -> Analysis SummaryType
checkReturn esumm f rv summ =
  case null nonNullRvs of
    -- Always returns NULL, not an allocator
    True -> return summ
    False -> do
      valid <- mapM (isAllocatedWithoutEscape esumm summ) nonNullRvs
      case and valid of
        False -> return summ
        True -> return $ M.insert f Nothing summ
  where
    rvs = flattenValue rv
    -- Here, drop all NULLs that are being returned since that is
    -- okay.  Also filter out Phi nodes (since we flattened the phi
    -- node to all of the values it could represent, but that list
    -- contains the phi node itself).
    nonNullRvs = filter isNotNull $ filter isNotPhi rvs

-- | Return True if the given Value is the result of a call to an
-- allocator AND does not escape.
isAllocatedWithoutEscape :: EscapeSummary -> SummaryType -> Value -> Analysis Bool
isAllocatedWithoutEscape esumm summ rv = do
  allocatorInsts <- case valueContent' rv of
    InstructionC i@CallInst { callFunction = f } ->
      checkFunctionIsAllocator f summ [i]
    InstructionC i@InvokeInst { invokeFunction = f } ->
      checkFunctionIsAllocator f summ [i]

    -- Returning a sub-object using safe addressing.  This also works
    -- for some forms of pointer arithmetic that LLVM lowers into a
    -- GEP instruction.  Something more general could be added for
    -- uglier cases, but this seems like a good compromise.
    InstructionC i@GetElementPtrInst { getElementPtrValue =
      (valueContent' -> InstructionC base@CallInst { callFunction = f })} ->
      checkFunctionIsAllocator f summ [i, base]
    InstructionC i@GetElementPtrInst { getElementPtrValue =
      (valueContent' -> InstructionC base@InvokeInst { invokeFunction = f })} ->
      checkFunctionIsAllocator f summ [i, base]

    _ -> return []
  -- If there are no values to check for escaping, this is not an
  -- allocator.  If there are values, none may escape.
  case null allocatorInsts of
    True -> return False
    False -> return $! noneEscape esumm allocatorInsts

checkFunctionIsAllocator :: Value -> SummaryType -> [Instruction] -> Analysis [Instruction]
checkFunctionIsAllocator v summ is =
  case valueContent' v of
    FunctionC f ->
      case M.lookup f summ of
        Nothing -> return []
        Just _ -> return is
    ExternalFunctionC f -> do
      depSumm <- asks dependencySummary
      case lookupFunctionSummary depSumm f of
        Nothing -> return []
        Just annots ->
          case any isAllocatorAnnot annots of
            False -> return []
            True -> return is
    InstructionC LoadInst { loadAddress = (valueContent' ->
      GlobalVariableC GlobalVariable { globalVariableInitializer = Just val0 })} ->
      checkFunctionIsAllocator val0 summ is
    -- Indirect call
    _ -> return []

noneEscape :: EscapeSummary -> [Instruction] -> Bool
noneEscape escSumm is = not (any (instructionEscapes escSumm) is)

-- Helpers

isAllocatorAnnot :: FuncAnnotation -> Bool
isAllocatorAnnot (FAAllocator _) = True
isAllocatorAnnot _ = False

isNotNull :: Value -> Bool
isNotNull v =
  case valueContent v of
    ConstantC ConstantPointerNull {} -> False
    _ -> True

isNotPhi :: Value -> Bool
isNotPhi v =
  case valueContent' v of
    InstructionC PhiNode {} -> False
    _ -> True

-- Testing

-- | Convert an Allocator summary to a format more suitable for
-- testing
allocatorSummaryToTestFormat :: AllocatorSummary -> Map String (Maybe String)
allocatorSummaryToTestFormat (AllocatorSummary s _) =
  M.mapKeys (show . functionName) s