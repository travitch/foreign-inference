{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns, DeriveGeneric, TemplateHaskell #-}
-- | This analysis identifies output parameters.
--
-- Output parameters are those pointer parameters whose target memory
-- is never read from, only written to.  This implies that the value
-- at the target of the pointer at the time of a call is irrelevant.
-- Bindings can then automatically manage these parameters for
-- callers.
--
-- It is a dataflow analysis that classifies pointer parameters as
-- input, output, or both.  The initial value for each pointer
-- parameter is unused and the meet operator is point-wise least upper
-- bound (LUB).
--
-- This analysis only deals with pointers to scalar types and pointers
-- to aggregates.  A pointer to an aggregate is an output parameter if
-- all of the fields of the aggregate are overwritten.
module Foreign.Inference.Analysis.Output (
  -- * Interface
  OutputSummary,
  identifyOutput,
  OutAnalysisConfig(..),
  defaultOutAnalysisConfig,

  -- * Testing
  outputSummaryToTestFormat
  ) where

import GHC.Generics ( Generic )

import Control.Arrow ( (&&&), second )
import Control.DeepSeq
import Control.DeepSeq.Generics ( genericRnf )
import Control.Lens ( Lens', makeLenses, lens, set, view, (%~), (^.) )
import Control.Monad ( foldM, guard )
import Data.List ( find, groupBy )
import Data.Map ( Map )
import qualified Data.Map as M
import Data.Maybe ( fromMaybe, mapMaybe )
import Data.Monoid
import Data.Set ( Set )
import qualified Data.Set as S
import Text.Printf

import LLVM.Analysis
import LLVM.Analysis.CFG
import LLVM.Analysis.CallGraphSCCTraversal
import LLVM.Analysis.Dataflow

import Foreign.Inference.AnalysisMonad
import Foreign.Inference.Diagnostics
import Foreign.Inference.Interface
import Foreign.Inference.Analysis.Allocator
import Foreign.Inference.Analysis.Escape

-- | Either the finalizer for an output argument, a token indicating
-- that the output argument was a NULL pointer, or a token indicating
-- that more than one out finalizer is involved.
data OutFinalizer = OutFinalizer String
                  | OutFinalizerNull
                  | OutFinalizerConflict
                  deriving (Eq, Ord)

data ArgumentDirection = ArgIn
                       | ArgOut
                       | ArgOutAlloc (Set Instruction, OutFinalizer)
                         -- ^ Instructions and their associated finalizer
                       | ArgBoth
                       deriving (Eq, Ord)

instance Show ArgumentDirection where
  show ArgIn = "in"
  show ArgOut = "out"
  show (ArgOutAlloc (_, OutFinalizer fin)) = printf "out[%s]" fin
  show (ArgOutAlloc (_, OutFinalizerNull)) = "out"
  show (ArgOutAlloc (_, OutFinalizerConflict)) = "out[?]"
  show ArgBoth = "both"

instance NFData ArgumentDirection

-- | Tracks the direction of each argument
type SummaryType = Map Argument (ArgumentDirection, [Witness])
-- | Tracks the direction of fields of pointer-to-struct arguments.
-- If all of the fields of a struct argument are ArgOut, the struct
-- argument is output.
type FieldSummaryType = Map (Argument, Int) (ArgumentDirection, [Witness])
data OutputSummary =
  OutputSummary { _outputSummary :: SummaryType
                , _outputFieldSummary :: FieldSummaryType
                , _outputDiagnostics :: Diagnostics
                }
  deriving (Generic)

$(makeLenses ''OutputSummary)

data OutInfo = OI { _outputInfo :: !(Map Argument (ArgumentDirection, Set Witness))
                  , _outputFieldInfo :: !(Map (Argument, Int) (ArgumentDirection, Set Witness))
                  }
             deriving (Eq, Show)

$(makeLenses ''OutInfo)

instance Eq OutputSummary where
  (OutputSummary s1 fs1 _) == (OutputSummary s2 fs2 _) =
    s1 == s2 && fs1 == fs2

instance Monoid OutputSummary where
  mempty = OutputSummary mempty mempty mempty
  mappend (OutputSummary s1 sf1 d1) (OutputSummary s2 sf2 d2) =
    OutputSummary (M.union s1 s2) (M.union sf1 sf2) (mappend d1 d2)

instance NFData OutputSummary where
  rnf = genericRnf

instance HasDiagnostics OutputSummary where
  diagnosticLens = outputDiagnostics

instance SummarizeModule OutputSummary where
  summarizeFunction _ _ = []
  summarizeArgument = summarizeOutArgument

summarizeOutArgument :: Argument -> OutputSummary -> [(ParamAnnotation, [Witness])]
summarizeOutArgument a (OutputSummary s sf _) =
  case M.lookup a s of
    Nothing ->
      case argumentFieldCount a of
        Nothing -> []
        Just flds ->
          let argFieldDirs = M.toList (M.filterWithKey (matchesArg a) sf)
          in case length argFieldDirs == flds && all isOutField argFieldDirs of
            False -> []
            True -> [(PAOut, combineWitnesses argFieldDirs)]

    Just (ArgIn, _) -> []
    Just (ArgOut, ws) -> [(PAOut, ws)]
    Just (ArgOutAlloc (_, OutFinalizer fin), ws) -> [(PAOutAlloc fin, ws)]
    Just (ArgOutAlloc (_, OutFinalizerNull), ws) -> [(PAOut, ws)]
    Just (ArgOutAlloc (_, OutFinalizerConflict), ws) -> [(PAOut, ws)]
    Just (ArgBoth, ws) -> [(PAInOut, ws)]


matchesArg :: Argument -> (Argument, a) -> b -> Bool
matchesArg a (ma, _) _ = ma == a

isOutField :: (a, (ArgumentDirection, b)) -> Bool
isOutField (_, (ArgOut, _)) = True
isOutField (_, (ArgOutAlloc _, _)) = True
isOutField _ = False

combineWitnesses :: [(a, (b, [Witness]))] -> [Witness]
combineWitnesses = concatMap (snd . snd)


-- | If the argument is a pointer to a struct, return the number of
-- fields in the struct.  Otherwise, return Nothing.
argumentFieldCount :: Argument -> Maybe Int
argumentFieldCount a =
  case argumentType a of
    TypePointer (TypeStruct _ flds _) _ -> Just (length flds)
    _ -> Nothing

data OutData = OD { moduleSummary :: OutputSummary
                  , allocatorSummary :: AllocatorSummary
                  , escapeSummary :: EscapeSummary
                  }

defaultOutAnalysisConfig :: OutAnalysisConfig
defaultOutAnalysisConfig = OAC False

data OutAnalysisConfig = OAC { trivialBlockHack :: Bool }

-- | Note that array parameters are not out parameters, so we rely on
-- the Array analysis to let us filter those parameters out of our
-- results.
identifyOutput :: forall compositeSummary funcLike . (FuncLike funcLike, HasCFG funcLike, HasFunction funcLike)
                  => OutAnalysisConfig
                  -> DependencySummary
                  -> Lens' compositeSummary OutputSummary
                  -> Lens' compositeSummary AllocatorSummary
                  -> Lens' compositeSummary EscapeSummary
                  -> ComposableAnalysis compositeSummary funcLike
identifyOutput conf ds lns allocLens escapeLens =
  composableDependencyAnalysisM runner (outAnalysis conf) lns depLens
  where
    runner a = runAnalysis a ds constData ()
    constData = OD mempty undefined undefined
    readerL = view allocLens &&& view escapeLens
    writerL csumm (a, e) = (set allocLens a . set escapeLens e) csumm
    depLens :: Lens' compositeSummary (AllocatorSummary, EscapeSummary)
    depLens = lens readerL writerL


meetDir :: ArgumentDirection -> ArgumentDirection -> ArgumentDirection
meetDir ArgIn ArgIn = ArgIn
meetDir ArgOut ArgOut = ArgOut
meetDir ArgOut (ArgOutAlloc _) = ArgOut
meetDir (ArgOutAlloc _) ArgOut = ArgOut
meetDir ArgIn ArgOut = ArgBoth
meetDir ArgOut ArgIn = ArgBoth
meetDir ArgIn (ArgOutAlloc _) = ArgBoth
meetDir (ArgOutAlloc _) ArgIn = ArgBoth

-- If the finalizers are different, consider this to just be a
-- normal out parameter since we can't say which finalizer is
-- involved.  We could possibly change this to at least tell the
-- user that ownership is transfered but the finalizer is unknown.
meetDir (ArgOutAlloc (is1, fin1)) (ArgOutAlloc (is2, fin2))
  | fin1 == fin2 = ArgOutAlloc (S.union is1 is2, fin1)
  | otherwise =
    case (fin1, fin2) of
      (OutFinalizerConflict, _) -> ArgOutAlloc (S.union is1 is2, OutFinalizerConflict)
      (_, OutFinalizerConflict) -> ArgOutAlloc (S.union is1 is2, OutFinalizerConflict)
      (OutFinalizerNull, OutFinalizerNull) -> ArgOutAlloc (mempty, OutFinalizerNull)
      (OutFinalizerNull, OutFinalizer f) -> ArgOutAlloc (is2, OutFinalizer f)
      (OutFinalizer f, OutFinalizerNull) -> ArgOutAlloc (is1, OutFinalizer f)
      _ -> ArgOutAlloc (S.union is1 is2, OutFinalizerConflict)

meetDir ArgBoth _ = ArgBoth
meetDir _ ArgBoth = ArgBoth

top :: OutInfo
top = OI mempty mempty

meetOutInfo :: OutInfo -> OutInfo -> OutInfo
meetOutInfo (OI m1 mf1) (OI m2 mf2) =
  OI (M.unionWith meetWithWitness m1 m2) (M.unionWith meetWithWitness mf1 mf2)
  where
    meetWithWitness (v1, w1) (v2, w2) = (meetDir v1 v2, S.union w1 w2)

type Analysis = AnalysisMonad OutData ()

outAnalysis :: (FuncLike funcLike, HasFunction funcLike, HasCFG funcLike)
               => OutAnalysisConfig
               -> (AllocatorSummary, EscapeSummary)
               -> funcLike
               -> OutputSummary
               -> Analysis OutputSummary
outAnalysis conf (allocSumm, escSumm) funcLike s = do
  let envMod e = e { moduleSummary = s
                   , allocatorSummary = allocSumm
                   , escapeSummary = escSumm
                   }
      analysis = dataflowAnalysis top meetOutInfo (outTransfer conf)
  funcInfo <- analysisLocal envMod (forwardDataflow funcLike analysis top)
  let OI exitInfo fexitInfo = dataflowResult funcInfo
      exitInfo' = M.map (second S.toList) exitInfo
      fexitInfo' = M.map (second S.toList) fexitInfo
  -- Merge the local information we just computed with the global
  -- summary.  Prefer the locally computed info if there are
  -- collisions (could arise while processing SCCs).
  return $! (outputSummary %~ M.union exitInfo') $ (outputFieldSummary %~ M.union fexitInfo') s

-- | If the given @callInst@ is an allocated value (i.e., call to an
-- allocator) and it does not escape via any means other than the
-- given @storeInst@ (which stored it into an 'Argument'), return the
-- name of its associated finalizer.
isAllocatedValue :: Instruction -> Value -> Instruction -> Analysis (Maybe String)
isAllocatedValue storeInst calledFunc callInst = do
  asum <- analysisEnvironment allocatorSummary
  esum <- analysisEnvironment escapeSummary
  annots <- lookupFunctionSummaryList asum calledFunc
  case mapMaybe isAllocAnnot annots of
    [fin] ->
      case instructionEscapesWith ignoreStore callInst esum of
        Nothing -> return $! Just fin
        Just _ -> return Nothing
    _ -> return Nothing
  where
    ignoreStore = (== storeInst)
    isAllocAnnot (FAAllocator fin) = Just fin
    isAllocAnnot _ = Nothing

-- | This transfer function only needs to be concerned with Load and
-- Store instructions (for now).  Loads add in an ArgIn value. Stores
-- add an ArgOut.
--
-- Note, we don't use valueContent' to strip bitcasts here since
-- accesses to bitfields use lots of interesting bitcasts and give us
-- false positives.
outTransfer :: OutAnalysisConfig -> OutInfo -> Instruction -> Analysis OutInfo
outTransfer conf info i =
  case i of
    LoadInst { loadAddress = (valueContent -> ArgumentC ptr) } ->
      return $! merge outputInfo i ptr ArgIn info
    StoreInst { storeAddress = (valueContent' -> ArgumentC ptr)
              , storeValue = (valueContent' -> InstructionC ci@CallInst {
                                 callFunction = f})} -> do
      allocFinalizer <- isAllocatedValue i f ci
      case allocFinalizer of
        Nothing -> return $! merge outputInfo i ptr ArgOut info
        Just fin -> return $! merge outputInfo i ptr (ArgOutAlloc (S.singleton ci, OutFinalizer fin)) info
    StoreInst { storeAddress = (valueContent' -> ArgumentC ptr)
              , storeValue = (valueContent' -> ConstantC ConstantPointerNull {})} ->
      return $! merge outputInfo i ptr (ArgOutAlloc (mempty, OutFinalizerNull)) info
    StoreInst { storeAddress = (valueContent -> ArgumentC ptr) } ->
      return $! merge outputInfo i ptr ArgOut info
    AtomicRMWInst { atomicRMWPointer = (valueContent -> ArgumentC ptr) } ->
      return $! merge outputInfo i ptr ArgBoth info
    AtomicCmpXchgInst { atomicCmpXchgPointer = (valueContent -> ArgumentC ptr) } ->
      return $! merge outputInfo i ptr ArgBoth info

    LoadInst { loadAddress = (valueContent -> InstructionC
      GetElementPtrInst { getElementPtrValue = (valueContent -> ArgumentC ptr)
                        , getElementPtrIndices = [ (valueContent -> ConstantC (ConstantInt _ _ 0))
                                                 , (valueContent -> ConstantC (ConstantInt _ _ fldNo))
                                                 ]
                        })} ->
      return $! merge outputFieldInfo i (ptr, fromIntegral fldNo) ArgIn info
    StoreInst { storeAddress = (valueContent -> InstructionC
      GetElementPtrInst { getElementPtrValue = (valueContent -> ArgumentC ptr)
                        , getElementPtrIndices = [ (valueContent -> ConstantC (ConstantInt _ _ 0))
                                                 , (valueContent -> ConstantC (ConstantInt _ _ fldNo))
                                                 ]
                        })} ->
      return $! merge outputFieldInfo i (ptr, fromIntegral fldNo) ArgOut info
    AtomicRMWInst { atomicRMWPointer = (valueContent -> InstructionC
      GetElementPtrInst { getElementPtrValue = (valueContent -> ArgumentC ptr)
                        , getElementPtrIndices = [ (valueContent -> ConstantC (ConstantInt _ _ 0))
                                                 , (valueContent -> ConstantC (ConstantInt _ _ fldNo))
                                                 ]
                        })} ->
      return $! merge outputFieldInfo i (ptr, fromIntegral fldNo) ArgBoth info
    AtomicCmpXchgInst { atomicCmpXchgPointer = (valueContent -> InstructionC
      GetElementPtrInst { getElementPtrValue = (valueContent -> ArgumentC ptr)
                        , getElementPtrIndices = [ (valueContent -> ConstantC (ConstantInt _ _ 0))
                                                 , (valueContent -> ConstantC (ConstantInt _ _ fldNo))
                                                 ]
                        })} ->
      return $! merge outputFieldInfo i (ptr, fromIntegral fldNo) ArgBoth info

    CallInst { callFunction = f, callArguments = args } ->
      callTransfer info i f (map fst args)
    InvokeInst { invokeFunction = f, invokeArguments = args }->
      callTransfer info i f (map fst args)

    BranchInst { branchTrueTarget = tt
               , branchFalseTarget = ft
               , branchCondition = (valueContent ->
      InstructionC ICmpInst { cmpV1 = v1, cmpV2 = v2
                            , cmpPredicate = p })} ->
        branchTransfer conf info i tt ft v1 v2 p

    _ -> return info

-- | The transfer function for branch instructions.  This has some special
-- handling of some interesting cases.  See Note [Pointers In Conditions]
branchTransfer :: OutAnalysisConfig
               -> OutInfo
               -> Instruction
               -> BasicBlock
               -> BasicBlock
               -> Value
               -> Value
               -> CmpPredicate
               -> Analysis OutInfo
branchTransfer conf info i tt ft v1 v2 p
  | trivialBlockHack conf && trivialNotNullBlock tt ft v1 v2 p = return info
  | otherwise =
    let args = mapMaybe fromValue [v1, v2]
    in return $ foldr (\x -> merge outputInfo i x ArgIn) info args

trivialNotNullBlock :: BasicBlock
                    -> BasicBlock
                    -> Value
                    -> Value
                    -> CmpPredicate
                    -> Bool
trivialNotNullBlock tt ft v1 v2 p = fromMaybe False $ do
  (bb, a) <- argumentAndNotNullBlock tt ft v1 v2 p
  -- To be a trivial block, the basic block @bb@ must have no function calls
  -- and only one store (and that must be to a).
  let (noCalls, storeToA, nStores) = foldr (trivialTestTransfer a) (True, False, 0) (basicBlockInstructions bb)
  guard (noCalls && storeToA && nStores == 1)
  return True

trivialTestTransfer :: Argument
                    -> Instruction
                    -> (Bool, Bool, Int)
                    -> (Bool, Bool, Int)
trivialTestTransfer a i acc@(noCalls, storeToA, nStores) =
  case i of
    CallInst {} -> (False, storeToA, nStores)
    InvokeInst {} -> (False, storeToA, nStores)
    StoreInst { storeAddress = (valueContent' -> ArgumentC sa) }
      | sa == a -> (noCalls, True, nStores + 1)
      | otherwise -> (noCalls, storeToA, nStores + 1)
    _ -> acc

-- | Return the input value that is not a constantpointernull, but fail
-- if /neither/ value is a constantpointernull.
argumentAndNotNullBlock :: BasicBlock
                        -> BasicBlock
                        -> Value
                        -> Value
                        -> CmpPredicate
                        -> Maybe (BasicBlock, Argument)
argumentAndNotNullBlock tt ft v1 v2 p =
  case (valueContent' v1, valueContent' v2) of
    (ConstantC ConstantPointerNull {}, ConstantC ConstantPointerNull {}) -> Nothing
    (ConstantC ConstantPointerNull {}, ArgumentC a) ->
      case p of
        ICmpNe -> return (ft, a)
        ICmpEq -> return (tt, a)
        _ -> Nothing
    (ArgumentC a, ConstantC ConstantPointerNull {}) ->
      case p of
        ICmpNe -> return (ft, a)
        ICmpEq -> return (tt, a)
        _ -> Nothing
    _ -> Nothing



isMemcpy :: Value -> Bool
isMemcpy v =
  case valueContent' v of
    ExternalFunctionC ExternalFunction { externalFunctionName = fname } ->
      show fname == "@llvm.memcpy.p0i8.p0i8.i32" || show fname == "@llvm.memcpy.p0i8.p0i8.i64"
    _ -> False


-- | A broken out transfer function for calls.  This deals with traversing
-- the list of arguments in a reasonable way to correctly handle argument
-- aliasing.  See Note [Argument Aliasing]
callTransfer :: OutInfo -> Instruction -> Value -> [Value] -> Analysis OutInfo
callTransfer info i f args = do
  let indexedArgs = zip [0..] args
  modSumm <- analysisEnvironment moduleSummary
  case (isMemcpy f, args) of
    (True, [dest, src, bytes, _, _]) ->
      memcpyTransfer info i dest src bytes
    _ -> do
      info' <- foldM (checkInArg modSumm) info indexedArgs
      foldM (checkOutArg modSumm) info' indexedArgs
  where
    checkInArg ms acc (ix, arg) =
      case valueContent' arg of
        ArgumentC a -> do
          attrs <- lookupArgumentSummaryList ms f ix
          case find isAnyOut attrs of
            Just _ -> return acc
            Nothing -> return $ merge outputInfo i a ArgIn acc
        _ -> return acc
    checkOutArg ms acc (ix, arg) =
      case valueContent' arg of
        ArgumentC a -> do
          attrs <- lookupArgumentSummaryList ms f ix
          case PAOut `elem` attrs of
            True -> return $! merge outputInfo i a ArgOut acc
            False ->
              case find isOutAllocAnnot attrs of
                Just (PAOutAlloc "") ->
                  return $! merge outputInfo i a (ArgOutAlloc (mempty, OutFinalizerConflict)) acc
                Just (PAOutAlloc fin) ->
                  return $! merge outputInfo i a (ArgOutAlloc (mempty, OutFinalizer fin)) acc
                Just _ -> return $! merge outputInfo i a ArgIn acc
                Nothing -> return $! merge outputInfo i a ArgIn acc
        _ -> return acc

isAnyOut :: ParamAnnotation -> Bool
isAnyOut (PAOutAlloc _) = True
isAnyOut PAOut = True
isAnyOut _ = False

isOutAllocAnnot :: ParamAnnotation -> Bool
isOutAllocAnnot (PAOutAlloc _) = True
isOutAllocAnnot _ = False

-- | FIXME: Be more robust and actually use the byte count to ensure it is a
-- full struct initialization.  In practice it probably always will be...
memcpyTransfer :: OutInfo -> Instruction -> Value -> Value -> Value -> Analysis OutInfo
memcpyTransfer info i dest src _ {-bytes-} =
  case (isArgument dest, isArgument src) of
    (Just darg, Just sarg) ->
      return $! merge outputInfo i darg ArgOut $ merge outputInfo i sarg ArgIn info
    (Just darg, Nothing) -> return $! merge outputInfo i darg ArgOut info
    (Nothing, Just sarg) -> return $! merge outputInfo i sarg ArgIn info
    _ -> return info
  where
    isArgument v =
      case valueContent' v of
        ArgumentC a -> Just a
        _ -> Nothing

merge :: (Ord k)
         => Lens' info (Map k (ArgumentDirection, Set Witness))
         -> Instruction -> k -> ArgumentDirection -> info -> info
merge lns i arg ArgBoth info =
  let ws = S.singleton (Witness i (show ArgBoth))
  in (lns %~ M.insert arg (ArgBoth, ws)) info
merge lns i arg newVal info =
  case M.lookup arg (info ^. lns) of
    -- No old value, so take the new one
    Nothing ->
      let ws = S.singleton (Witness i (show newVal))
      in (lns %~ M.insert arg (newVal, ws)) info
    -- The old value was Both, so just keep it
    Just (ArgBoth, _) -> info
    -- Since the new value is not Both, we can't advance from Out with
    -- linear control flow (only at control flow join points).
    Just (ArgOut, _) -> info
    -- We can actually override an OutAlloc with an Out if it comes
    -- later...  then the OutAlloc value is lost to the caller
    Just (ArgOutAlloc _, ws) ->
      case newVal of
        ArgOut ->
          let nw = Witness i (show ArgOut)
          in (lns %~ M.insert arg (ArgOut, S.singleton nw)) info
        ArgIn -> info
        ArgOutAlloc _ -> info -- FIXME: This should probably merge the two... or take newval
        ArgBoth -> error "Foreign.Inference.Analysis.Output.merge(1): Infeasible path"
    Just (ArgIn, ws) ->
      case newVal of
        ArgOut ->
          let nw = Witness i (show ArgBoth)
          in (lns %~ M.insert arg (ArgBoth, S.insert nw ws)) info
        ArgOutAlloc _ ->
          let nw = Witness i (show ArgBoth)
          in (lns %~ M.insert arg (ArgBoth, S.insert nw ws)) info
        ArgIn -> info
        ArgBoth -> error "Foreign.Inference.Analysis.Output.merge(2): Infeasible path"

removeArrayPtr :: Argument -> OutInfo -> OutInfo
removeArrayPtr a (OI oi foi) = OI (M.delete a oi) foi

-- Testing

-- | Convert an Output summary to a format more suitable for
-- testing
outputSummaryToTestFormat :: OutputSummary -> Map String (Set (String, ParamAnnotation))
outputSummaryToTestFormat (OutputSummary s sf _) =
  M.union scalarParams aggregateParams
  where
    scalarParams = foldr collectArgs mempty (M.toList s)

    aggList = groupBy sameArg (M.toList sf)
    aggListByArg = map flattenArg aggList
    aggregateParams = foldr collectAggArgs mempty aggListByArg

    sameArg ((a, _), _) ((b, _), _) = a == b
    flattenArg :: [((Argument, Int), (ArgumentDirection, [Witness]))]
                  -> (Argument, [(Int, ArgumentDirection)])
    flattenArg allFields@(((a, _), _) : _) =
      (a, map flatten' allFields)
    flattenArg [] = error "Foreign.Inference.Analysis.Output.outputSummaryToTestFormat: groupBy made an empty group"
    flatten' ((_, ix), (dir, _)) = (ix, dir)

    dirToAnnot d =
      case d of
        ArgIn -> Nothing
        ArgOut -> Just PAOut
        -- If the only out alloc case is a NULL pointer, treat it as a
        -- normal Out param
        ArgOutAlloc (_, OutFinalizerNull) -> Just PAOut
        ArgOutAlloc (_, OutFinalizer f) -> Just (PAOutAlloc f)
        ArgOutAlloc (_, OutFinalizerConflict) -> Just (PAOutAlloc "")
        ArgBoth -> Just PAInOut

    isOut (_, argDir) = argDir == ArgOut

    collectAggArgs (arg, fieldDirections) acc =
      let func = argumentFunction arg
          funcName = show (functionName func)
          argName = show (argumentName arg)
      in case argumentFieldCount arg of
        Nothing -> error ("Expected aggregate type in field direction summary " ++ show arg)
        Just fldCnt ->
          case length fieldDirections == fldCnt && all isOut fieldDirections of
            False -> acc
            True ->
              let nv = S.singleton (argName, PAOut)
              in M.insertWith' S.union funcName nv acc

    collectArgs (arg, (dir, _)) acc =
      let func = argumentFunction arg
          funcName = show (functionName func)
          argName = show (argumentName arg)
      in case dirToAnnot dir of
        Nothing -> acc
        Just annot ->
          let nv = S.singleton (argName, annot)
          in M.insertWith' S.union funcName nv acc

{- Note [Pointers In Conditions]

Reading the value of a pointer (the address - not the value in the location
pointed to) makes the pointer an input pointer.  This is because passing in
a non-NULL pointer offers different behavior compared to passing in a NULL
pointer.  Users have control over what action is taken.

This poses a slight problem for some parameters that we might want to treat
as output parameters:

> void foo(int *f) {
>   if(f) {
>     *f = x->y->z;
>   }
> }

According to the above algorithm, @f@ is an in/out parameter.  With the
@trivialBlockHack@ (which defaults to off), this example is treated as an
output paramter.  The trivial block hack says that a pointer parameter in a
conditional is *not* an input parameter iff the successor block in which it is
not null is /trivial/.  Here, trivial is defined as executing no side effects
besides the assignment through @f@.

With this definition, any side effects guarded by an out parameter are
preserved and the out parameter becomes in/out.  In this restricted case,
we allow an exception because we can safely allocate storage and lose nothing
by automating the process.

-}

{- Note [Argument Aliasing]

Aliased arguments require delicate treatment.  Consider a call like

> callee(param1, param1);

where the first parameter of callee is an output parameter and the second
is an input parameter.  If we just processed the arguments left-to-right,
param1 would become an output parameter (since OUT `meet` IN is OUT).  However,
that isn't quite right.  It is used as an input parameter to @callee@, so
it should really be IN/OUT.  We want to treat all of the effects of @callee@ as
happening simultaneously.

We can do that by first checking to see if any arguments are used as input
parameters.  Then process the argument list again to look for output
parameters, performing the standard merge operation.  We could add another
pre-pass for IN/OUT parameters as well.

See test output/aliasedParameterOut.c

-}

