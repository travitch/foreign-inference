{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell, ViewPatterns, DeriveGeneric #-}
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

import GHC.Generics ( Generic )

import Control.Arrow ( (&&&) )
import Control.DeepSeq
import Control.DeepSeq.Generics ( genericRnf )
import Control.Lens ( Simple, lens, view, set, (^.), (.~), makeLenses )
import Data.Map ( Map )
import qualified Data.Map as M
import Data.Maybe ( isJust )
import Data.Monoid
import Data.HashSet ( HashSet )
import qualified Data.HashSet as HS

import LLVM.Analysis
import LLVM.Analysis.CallGraphSCCTraversal

import Foreign.Inference.AnalysisMonad
import Foreign.Inference.Diagnostics
import Foreign.Inference.Interface
import Foreign.Inference.Analysis.Escape
import Foreign.Inference.Analysis.Finalize
import Foreign.Inference.Analysis.IndirectCallResolver
import Foreign.Inference.Internal.FlattenValue

-- import Text.Printf
-- import Debug.Trace
-- debug = flip trace

type SummaryType = HashSet Function
data AllocatorSummary =
  AllocatorSummary { _allocatorSummary :: SummaryType
                   , _allocatorDiagnostics :: Diagnostics
                   , _finalizerSummary :: FinalizerSummary
                   }
  deriving (Generic)

$(makeLenses ''AllocatorSummary)

instance Eq AllocatorSummary where
  (AllocatorSummary s1 _ _) == (AllocatorSummary s2 _ _) = s1 == s2

instance Monoid AllocatorSummary where
  mempty = AllocatorSummary mempty mempty mempty
  mappend (AllocatorSummary s1 d1 f1) (AllocatorSummary s2 d2 f2) =
    AllocatorSummary (HS.union s1 s2) (mappend d1 d2) (mappend f1 f2)

instance NFData AllocatorSummary where
  rnf = genericRnf

instance HasDiagnostics AllocatorSummary where
  diagnosticLens = allocatorDiagnostics

data AllocatorData =
  AllocatorData { dependencySummary :: DependencySummary
                , indirectCallSummary :: IndirectCallSummary
                }

type Analysis = AnalysisMonad AllocatorData ()

instance SummarizeModule AllocatorSummary where
  summarizeArgument _ _ = []
  summarizeFunction f (AllocatorSummary summ _ finSumm)
    | not (HS.member f summ) = []
    | otherwise =
        case automaticFinalizersForType finSumm (functionReturnType f) of
          -- If there is no allocator, assume we just free it...  this
          -- isn't necessarily safe.
          [] -> [FAAllocator "free"]
          [fin] -> [FAAllocator (identifierAsString (functionName fin))]
          -- There was more than one, can't guess
          _ -> [FAAllocator ""]

identifyAllocators :: forall compositeSummary funcLike . (FuncLike funcLike, HasFunction funcLike)
                      => DependencySummary
                      -> IndirectCallSummary
                      -> Simple Lens compositeSummary AllocatorSummary
                      -> Simple Lens compositeSummary EscapeSummary
                      -> Simple Lens compositeSummary FinalizerSummary
                      -> ComposableAnalysis compositeSummary funcLike
identifyAllocators ds ics lns escLens finLens =
  composableDependencyAnalysisM runner allocatorAnalysis lns depLens
  where
    runner a = runAnalysis a readOnlyData ()
    readOnlyData = AllocatorData ds ics
    depLens :: Simple Lens compositeSummary (EscapeSummary, FinalizerSummary)
    depLens = lens (view escLens &&& view finLens) (\csum (e, f) -> (set escLens e . set finLens f) csum)

-- | If the function returns a pointer, it is a candidate for an
-- allocator.  We do not concern ourselves with functions that may
-- unwind or call exit on error - these can also be allocators.
allocatorAnalysis :: (FuncLike funcLike, HasFunction funcLike)
                     => (EscapeSummary, FinalizerSummary)
                     -> funcLike
                     -> AllocatorSummary
                     -> Analysis AllocatorSummary
allocatorAnalysis (esumm, fsumm) funcLike s =
  case exitInst of
    RetInst { retInstValue = Just rv } ->
      case valueType rv of
        -- The function always returns a pointer
        TypePointer _ _ -> do
          s' <- checkReturn esumm f rv s
          return $! s' { _finalizerSummary = fsumm }
        -- Non-pointer return, ignore
        _ -> return s { _finalizerSummary = fsumm }
    -- Returns void
    _ -> return s { _finalizerSummary = fsumm }
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
checkReturn :: EscapeSummary -> Function -> Value -> AllocatorSummary -> Analysis AllocatorSummary
checkReturn esumm f rv summ
  -- Always returns NULL, not an allocator
  | null nonNullRvs = return summ
  | otherwise = do
    valid <- mapM (isAllocatedWithoutEscape esumm summ) nonNullRvs
    case and valid of
      False -> return summ
      True ->
        let summ' = HS.insert f (summ ^. allocatorSummary)
        in return $! (allocatorSummary .~ summ') summ
  where
    rvs = flattenValue rv
    -- Here, drop all NULLs that are being returned since that is
    -- okay.  Also filter out Phi nodes (since we flattened the phi
    -- node to all of the values it could represent, but that list
    -- contains the phi node itself).
    nonNullRvs = filter isNotNull $ filter isNotPhi rvs

-- | Return True if the given Value is the result of a call to an
-- allocator AND does not escape.
isAllocatedWithoutEscape :: EscapeSummary -> AllocatorSummary -> Value -> Analysis Bool
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

checkFunctionIsAllocator :: Value -> AllocatorSummary -> [Instruction] -> Analysis [Instruction]
checkFunctionIsAllocator v summ is =
  case valueContent' v of
    InstructionC LoadInst { } -> do
      sis <- analysisEnvironment indirectCallSummary
      case indirectCallInitializers sis v of
        [] -> return []
        [i] -> checkFunctionIsAllocator i summ is
        _ -> return []
    _ -> do
      depSumm <- analysisEnvironment dependencySummary
      case lookupFunctionSummary depSumm summ v of
        Nothing -> return []
        Just annots ->
          case any isAllocatorAnnot annots of
            False -> return []
            True -> return is

noneEscape :: EscapeSummary -> [Instruction] -> Bool
noneEscape escSumm is = not (any (isJust . flip escapeTest escSumm) is)
  where
    escapeTest = instructionEscapesWith ignoreReturn
    ignoreReturn i =
      case i of
        RetInst {} -> True
        _ -> False

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
allocatorSummaryToTestFormat (AllocatorSummary s _ _) =
  M.fromList $ map ((show . functionName) &&& const Nothing) $ HS.toList s

{-# ANN module "HLint: ignore Use if" #-}