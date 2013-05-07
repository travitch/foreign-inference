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
import Control.Lens ( Getter, Lens', view, (&), (.~), (%~), makeLenses, to )
import Control.Monad ( foldM )
import qualified Data.Foldable as F
import Data.Map ( Map )
import qualified Data.Map as M
import Data.Maybe ( catMaybes, isJust )
import Data.Monoid
import Data.Set ( Set )
import qualified Data.Set as S

import LLVM.Analysis
import LLVM.Analysis.CFG
import LLVM.Analysis.CallGraphSCCTraversal
import LLVM.Analysis.Dataflow

import Foreign.Inference.AnalysisMonad
import Foreign.Inference.Diagnostics
import Foreign.Inference.Interface
import Foreign.Inference.Analysis.Escape
import Foreign.Inference.Analysis.Finalize
import Foreign.Inference.Analysis.IndirectCallResolver
import Foreign.Inference.Analysis.Output
import Foreign.Inference.Internal.FlattenValue

-- import Text.Printf
-- import Debug.Trace
-- debug = flip trace

-- | The summary tracks the functions that return newly allocated values
-- through their normal return value.  It also tracks the output parameters
-- through which newly allocated values are returned.
data SummaryType = ST { _summaryAllocatorFuncs :: Set Function
                      , _summaryAllocatorArgs :: Set Argument
                      }
                      deriving (Generic, Eq, Show)

$(makeLenses ''SummaryType)

instance Monoid SummaryType where
  mempty = ST mempty mempty
  mappend (ST f1 a1) (ST f2 a2) = ST (mappend f1 f2) (mappend a1 a2)

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
    AllocatorSummary (mappend s1 s2) (mappend d1 d2) (mappend f1 f2)

instance NFData AllocatorSummary where
  rnf = genericRnf

instance NFData SummaryType where
  rnf = genericRnf

instance HasDiagnostics AllocatorSummary where
  diagnosticLens = allocatorDiagnostics

data AllocatorData =
  AllocatorData { indirectCallSummary :: IndirectCallSummary
                }

-- | This is the dataflow fact.  @allocatorReturnValues@ is the set of values
-- returned through the return instruction.  The values are flattened (and
-- thus phi-free).  The 'Instruction' paired with each value is the return
-- instruction that returned it.
--
-- @allocatorOutValues@ are the values returned through output parameters,
-- along with the Store instruction that returned them.  The Maybe wrapper
-- is used to accommodate transitive out allocations.  If there is a Nothing
-- in the return value set for an 'Argument', that means that the 'Argument'
-- was written to by a transitive output allocation.
--
-- These 'Instruction' tags are required for the escape analysis.  We know
-- that the allocated value escapes through its return slot - that is the
-- point.  The escape analysis needs to be told to ignore this known and
-- expected escape, so we track the responsibe instruction.
data AllocatorInfo =
  AI { _allocatorReturnValues :: Set (Value, Instruction)
     , _allocatorOutValues :: Map Argument (Set (Maybe (Value, Instruction)))
     }
     deriving (Eq, Show)

$(makeLenses ''AllocatorInfo)

type Analysis = AnalysisMonad AllocatorData ()

instance SummarizeModule AllocatorSummary where
  summarizeArgument a (AllocatorSummary (ST _ summ) _ finSumm)
    | not (S.member a summ) = []
    | otherwise =
      case automaticFinalizersForType finSumm (valueType a) of
        [] -> [(PAOutAlloc "free", [])]
        [fin] -> [(PAOutAlloc (identifierAsString (functionName fin)), [])]
        _ -> [(PAOutAlloc "", [])]
  summarizeFunction f (AllocatorSummary (ST summ _) _ finSumm)
    | not (S.member f summ) = []
    | otherwise =
        case automaticFinalizersForType finSumm (functionReturnType f) of
          -- If there is no allocator, assume we just free it...  this
          -- isn't necessarily safe.
          [] -> [(FAAllocator "free", [])]
          [fin] -> [(FAAllocator (identifierAsString (functionName fin)), [])]
          -- There was more than one, can't guess
          _ -> [(FAAllocator "", [])]

identifyAllocators :: forall compositeSummary funcLike . (FuncLike funcLike, HasFunction funcLike, HasCFG funcLike)
                      => DependencySummary
                      -> IndirectCallSummary
                      -> Lens' compositeSummary AllocatorSummary
                      -> Getter compositeSummary EscapeSummary
                      -> Getter compositeSummary FinalizerSummary
                      -> Getter compositeSummary OutputSummary
                      -> ComposableAnalysis compositeSummary funcLike
identifyAllocators ds ics lns escLens finLens outLens =
  composableDependencyAnalysisM runner allocatorAnalysis lns depLens
  where
    runner a = runAnalysis a ds readOnlyData ()
    readOnlyData = AllocatorData ics
    depLens :: Getter compositeSummary (EscapeSummary, (FinalizerSummary, OutputSummary))
    depLens = to (view escLens &&& (view finLens &&& view outLens))

-- | If the function returns a pointer, it is a candidate for an
-- allocator.  We do not concern ourselves with functions that may
-- unwind or call exit on error - these can also be allocators.

-- | If any return slot (return value or output parameter) returns only
-- non-escaping newly-allocated values, that return slot allocates.
allocatorAnalysis :: (FuncLike funcLike, HasFunction funcLike, HasCFG funcLike)
                     => (EscapeSummary, (FinalizerSummary, OutputSummary))
                     -> funcLike
                     -> AllocatorSummary
                     -> Analysis AllocatorSummary
allocatorAnalysis (esumm, (fsumm, outSumm)) funcLike s = do
  res <- forwardDataflow funcLike analysis top
  let AI rvs argRets = dataflowResult res
      s' = s & finalizerSummary .~ fsumm
  s'' <- checkReturnValues esumm f (S.toList rvs) s'
  foldM (checkArgValues esumm) s'' (M.toList argRets)
  where
    f = getFunction funcLike
    analysis = dataflowAnalysis top meet (transfer s outSumm)

top :: AllocatorInfo
top = AI mempty mempty

meet :: AllocatorInfo -> AllocatorInfo -> AllocatorInfo
meet (AI r1 a1) (AI r2 a2) =
  AI (r1 `mappend` r2) (M.unionWith S.union a1 a2)

-- | The transfer function for returns is cumulative since those end
-- execution.  I haven't seen more than one return instruction in a
-- function before, but this code handles it.
--
-- The transfer function for stores overwrites previous values, since the
-- caller sees only the last value stored.  The meet operator still unions.
--
-- Transitive out allocations work just like Stores, except no value needs to
-- be checked and the responsible instruction does not need to be recorded.
transfer :: AllocatorSummary
         -> OutputSummary
         -> AllocatorInfo
         -> Instruction
         -> Analysis AllocatorInfo
transfer s outSumm ai i =
  case i of
    RetInst { retInstValue = Just rv }
      | isPointerType (valueType rv) ->
        let rvs = S.fromList (zip (flattenValue rv) (repeat i))
        in return $! ai & allocatorReturnValues %~ S.union rvs
      | otherwise -> return ai
    StoreInst { storeAddress = (valueContent' -> ArgumentC arg)
              , storeValue = (stripBitcasts -> sv)
              }
      | isOutParam outSumm arg ->
        let rvs = S.fromList $ map Just (zip (flattenValue sv) (repeat i))
        in return $! ai & allocatorOutValues %~ M.insert arg rvs
      | otherwise -> return ai
    CallInst { callFunction = cf, callArguments = (map fst -> args) } ->
      foldM (argumentTransfer s cf) ai (zip [0..] args)
    InvokeInst { invokeFunction = cf, invokeArguments = (map fst -> args) } ->
      foldM (argumentTransfer s cf) ai (zip [0..] args)
    _ -> return ai

argumentTransfer :: AllocatorSummary
                 -> Value
                 -> AllocatorInfo
                 -> (Int, Value)
                 -> Analysis AllocatorInfo
argumentTransfer s cf ai (ix, (valueContent' -> ArgumentC a)) = do
  summ <- lookupArgumentSummaryList s cf ix
  case any isOutAlloc summ of
    False -> return ai
    True -> return $! ai & allocatorOutValues %~ M.insert a (S.singleton Nothing)
argumentTransfer _ _ ai _ = return ai

isOutAlloc :: ParamAnnotation -> Bool
isOutAlloc (PAOutAlloc _) = True
isOutAlloc _ = False

isOutParam :: OutputSummary -> Argument -> Bool
isOutParam s a = PAOut `elem` map fst (summarizeArgument a s)

isPointerType :: Type -> Bool
isPointerType (TypePointer _ _) = True
isPointerType _ = False

-- | The set we are looking at has Maybes.  The 'Nothing' values indicate
-- out-alloc parameters.  There is nothing else to check there because
-- we know those are allocators.  We do need to make sure that we don't
-- completely ignore them in the null check, though. 
checkArgValues :: EscapeSummary
               -> AllocatorSummary
               -> (Argument, Set (Maybe (Value, Instruction)))
               -> Analysis AllocatorSummary
checkArgValues esumm summ (a, S.toList -> rvs)
  | null nonNullRvs && not hasOutAlloc = return summ
  | otherwise = do
    valid <- mapM (isAllocatedWithoutEscape esumm summ) nonNullRvs
    case and valid of
      False -> return summ
      True ->
        return $! summ & (allocatorSummary . summaryAllocatorArgs) %~ S.insert a
  where
    hasOutAlloc = any (==Nothing) rvs
    nonNullRvs = filter (mayBeAlloc . fst) (catMaybes rvs)

-- | If the return value is always one of:
--
--  * NULL
--
--  * The result of an allocator (and does not escape)
--
-- then f is an allocator.  If there is a unique finalizer for the
-- same type, associate it with this allocator.
checkReturnValues :: EscapeSummary
                  -> Function
                  -> [(Value, Instruction)]
                  -> AllocatorSummary
                  -> Analysis AllocatorSummary
checkReturnValues esumm f rvs summ
  -- Always returns NULL, not an allocator
  | null nonNullRvs = return summ
  | otherwise = do
    valid <- mapM (isAllocatedWithoutEscape esumm summ) nonNullRvs
    case and valid of
      False -> return summ
      True ->
        return $! summ & (allocatorSummary . summaryAllocatorFuncs) %~ S.insert f
  where
    -- Here, drop all NULLs that are being returned since that is
    -- okay.  Also filter out Phi nodes (since we flattened the phi
    -- node to all of the values it could represent, but that list
    -- contains the phi node itself).
    nonNullRvs = filter (mayBeAlloc . fst) rvs


-- | Return True if the given Value is the result of a call to an
-- allocator AND does not escape.
isAllocatedWithoutEscape :: EscapeSummary
                         -> AllocatorSummary
                         -> (Value, Instruction)
                         -> Analysis Bool
isAllocatedWithoutEscape esumm summ (rv, escInst) = do
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
    False -> return $! noneEscape esumm allocatorInsts escInst

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
      annots <- lookupFunctionSummaryList summ v
      case any isAllocatorAnnot annots of
        False -> return []
        True -> return is

noneEscape :: EscapeSummary -> [Instruction] -> Instruction -> Bool
noneEscape escSumm is returnSlot =
  not (any (isJust . flip (escapeTest returnSlot) escSumm) is)
  where
    escapeTest rs = instructionEscapesWith (==rs)

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

mayBeAlloc :: Value -> Bool
mayBeAlloc x = all ($ x) [isNotNull, isNotPhi]

-- Testing

-- | Convert an Allocator summary to a format more suitable for
-- testing
allocatorSummaryToTestFormat :: AllocatorSummary
                             -> (Map String (Maybe String), Map String (Set (String, ParamAnnotation)))
allocatorSummaryToTestFormat summ@(AllocatorSummary (ST fs args) _ _) =
  (fannots, argAnnots)
  where
    fannots = M.fromList $ map ((show . functionName) &&& const Nothing) $ S.toList fs
    argAnnots = F.foldr toArgSumm mempty args
    toArgSumm a m =
      let f = identifierAsString (functionName (argumentFunction a))
          aname = identifierAsString (argumentName a)
      in case summarizeArgument a summ of
        [(annot@(PAOutAlloc _), _)] ->
          M.insertWith S.union f (S.singleton (aname, annot)) m
        _ -> m


{-# ANN module "HLint: ignore Use if" #-}
