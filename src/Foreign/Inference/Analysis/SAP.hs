{-# LANGUAGE TemplateHaskell, DeriveGeneric, ViewPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
-- | An analysis to identify @Symbolic Access Paths@ for each function
-- in a Module.
module Foreign.Inference.Analysis.SAP (
  SAPSummary,
  identifySAPs,
  finalizedPaths,
  returnedPaths,
  writePaths,
  -- * Testing
  sapReturnResultToTestFormat,
  sapArgumentResultToTestFormat,
  sapFinalizeResultToTestFormat
  ) where

import GHC.Generics ( Generic )

import Control.Arrow ( (&&&) )
import Control.DeepSeq
import Control.DeepSeq.Generics ( genericRnf )
import Control.Lens ( Simple, makeLenses, (%~), (.~), (^.), set, view, lens )
import Control.Monad ( foldM )
import qualified Data.Foldable as F
import Data.Map ( Map )
import qualified Data.Map as M
import Data.Maybe ( fromMaybe, mapMaybe )
import Data.Monoid
import Data.Set ( Set )
import qualified Data.Set as S
import Safe.Failure ( at )

import LLVM.Analysis
import LLVM.Analysis.AccessPath
import LLVM.Analysis.CallGraphSCCTraversal

import Foreign.Inference.AnalysisMonad
import Foreign.Inference.Analysis.Finalize
import Foreign.Inference.Analysis.SAPPTRel
import Foreign.Inference.Diagnostics
import Foreign.Inference.Interface

-- | Argument being stored into, Access path into that argument, and
-- the argument being stored.
data WritePath = WritePath !Int AbstractAccessPath
               deriving (Eq, Ord, Show, Generic)

-- | An argument field that is finalized
data FinalizePath = FinalizePath AbstractAccessPath
                  deriving (Eq, Ord, Show, Generic)

-- | A path from an argument that is returned.
data ReturnPath = ReturnPath !Int AbstractAccessPath
                deriving (Eq, Ord, Show, Generic)

instance NFData WritePath where
  rnf = genericRnf

instance NFData FinalizePath where
  rnf = genericRnf

instance NFData ReturnPath where
  rnf = genericRnf

data SAPSummary =
  SAPSummary { _sapReturns :: Map Function (Set ReturnPath)
               -- ^ The return paths for each function
             , _sapArguments :: Map Argument (Set WritePath)
               -- ^ Maps each Argument to the access paths it is
               -- stored into.
             , _sapFinalize :: Map Argument (Set FinalizePath)
               -- ^ Maps each Argument to the access paths based on it
               -- that are finalized.
             , _sapDiagnostics :: Diagnostics
             }
  deriving (Generic)

$(makeLenses ''SAPSummary)

finalizedPaths :: Argument -> SAPSummary -> Maybe [AbstractAccessPath]
finalizedPaths a (SAPSummary _ _ fs _) = do
  fps <- M.lookup a fs
  return $ map (\(FinalizePath p) -> p) $ S.toList fps

-- | Get the paths that function @f@ returns from its argument @a@
returnedPaths :: Function -> Argument -> SAPSummary -> Maybe [AbstractAccessPath]
returnedPaths f a (SAPSummary rs _ _ _) = do
  rps <- M.lookup f rs
  let aix = argumentIndex a
      unwrap (ReturnPath ix p) =
        case ix == aix of
          True -> return p
          False -> Nothing
  return $ mapMaybe unwrap (S.toList rps)

writePaths :: Argument -> SAPSummary -> Maybe [(Argument, AbstractAccessPath)]
writePaths a (SAPSummary _ ws _ _) = do
  wps <- M.lookup a ws
  return $ mapMaybe unwrap (S.toList wps)
  where
    unwrap (WritePath ix p) = do
      arg <- args `at` ix
      return (arg, p)
    f = argumentFunction a
    args = functionParameters f

instance Eq SAPSummary where
  (SAPSummary r1 a1 f1 _) == (SAPSummary r2 a2 f2 _) =
    r1 == r2 && a1 == a2 && f1 == f2

instance Monoid SAPSummary where
  mempty = SAPSummary mempty mempty mempty mempty
  mappend (SAPSummary r1 a1 f1 d1) (SAPSummary r2 a2 f2 d2) =
    SAPSummary { _sapReturns = M.union r1 r2
               , _sapArguments = M.unionWith S.union a1 a2
               , _sapFinalize = M.unionWith S.union f1 f2
               , _sapDiagnostics = d1 `mappend` d2
               }

instance NFData SAPSummary where
  rnf = genericRnf

instance HasDiagnostics SAPSummary where
  diagnosticLens = sapDiagnostics

type Analysis = AnalysisMonad () ()

instance SummarizeModule SAPSummary where
  summarizeArgument a (SAPSummary _ as fs _) =
    let externalizeWrite (WritePath ix p) =
          (ix, show (abstractAccessPathBaseType p), abstractAccessPathComponents p)
        externalizeFinalize (FinalizePath p) =
          (show (abstractAccessPathBaseType p), abstractAccessPathComponents p)
        toAnnot con elts = [(con elts, [])]
        fs' = maybe [] (toAnnot PAFinalizeField . map externalizeFinalize . S.toList) (M.lookup a fs)
        as' = maybe [] (toAnnot PASAPWrite . map externalizeWrite . S.toList) (M.lookup a as)
    in fs' ++ as'

  summarizeFunction f (SAPSummary rs _ _ _) =
    fromMaybe [] $ do
      fr <- M.lookup f rs
      let toExternal (ReturnPath ix p) =
            (ix, show (abstractAccessPathBaseType p), abstractAccessPathComponents p)
      return [(FASAPReturn $ map toExternal $ S.toList fr, [])]

identifySAPs :: forall compositeSummary funcLike .
                (FuncLike funcLike, HasFunction funcLike)
                => DependencySummary
                -> Simple Lens compositeSummary SAPSummary
                -> Simple Lens compositeSummary SAPPTRelSummary
                -> Simple Lens compositeSummary FinalizerSummary
                -> ComposableAnalysis compositeSummary funcLike
identifySAPs ds lns ptrelL finL =
  composableDependencyAnalysisM runner sapAnalysis lns depLens
  where
    runner a = runAnalysis a ds () ()
    readL = view ptrelL &&& view finL
    writeL csum (s, f) = (set ptrelL s . set finL f) csum
    depLens :: Simple Lens compositeSummary (SAPPTRelSummary, FinalizerSummary)
    depLens = lens readL writeL

-- | For non-void functions, first check the return instruction and
-- see if it is returning some access path.  Next, just iterate over
-- all stores.
--
-- At call intructions, extend callee paths that are passed some path
-- based on an argument.
sapAnalysis :: (FuncLike funcLike, HasFunction funcLike)
               => (SAPPTRelSummary, FinalizerSummary)
               -> funcLike
               -> SAPSummary
               -> Analysis SAPSummary
sapAnalysis (ptrelSumm, finSumm) flike s =
  foldM (sapTransfer f ptrelSumm finSumm) s (functionInstructions f)
  where
    f = getFunction flike

sapTransfer :: Function
               -> SAPPTRelSummary
               -> FinalizerSummary
               -> SAPSummary
               -> Instruction
               -> Analysis SAPSummary
sapTransfer f ptrelSumm finSumm s i =
  case i of
    RetInst { retInstValue = Just (valueContent' ->
      InstructionC PhiNode { phiIncomingValues = (map fst -> ivs) })} ->
      foldM (returnValueTransfer f) s (valuesAsInsts ivs)
    RetInst { retInstValue = Just (valueContent' ->
      InstructionC SelectInst { selectTrueValue = tv, selectFalseValue = fv })} ->
      foldM (returnValueTransfer f) s (valuesAsInsts [tv, fv])
    RetInst { retInstValue = Just (valueContent' -> InstructionC ri) } ->
      returnValueTransfer f s ri

    -- We need to make an entry in sapArguments if we store an argument
    -- into some access path based on another argument
    --
    -- FIXME: If we are storing into the result of a callinst, check
    -- to see if that call has a summary that could be extended.
    StoreInst { storeValue = (valueContent' -> ArgumentC sv) } ->
      storeTransfer ptrelSumm s sv

    CallInst { callFunction = callee
             , callArguments = (map fst -> actuals) } ->
      foldM (callTransfer finSumm callee actuals) s (zip [0..] actuals)
    InvokeInst { invokeFunction = callee
               , invokeArguments = (map fst -> actuals) } ->
      foldM (callTransfer finSumm callee actuals) s (zip [0..] actuals)

    _ -> return s

-- | If we are calling a function that, as a side-effect, stores one
-- of its arguments into a field of another, we need to stitch
-- together the access paths (as in the transitive return call case).
-- This propagates information about the _store_ case to callers.
--
-- > void g(struct S *s, int *x) {
-- >   s->f1 = x;
-- > }
-- >
-- > void f(struct T *t, int *x) {
-- >   g(t->s, x);
-- > }
--
-- The summary for @g@ is produced by the _store_ case.  This function
-- produces the summary for @f@ based on the call to @g@.  This
-- function is called once for each actual argument to the call of @g@
-- by the top-level transfer function.
callTransfer :: FinalizerSummary
                -> Value
                -> [Value]
                -> SAPSummary
                -> (Int, Value)
                -> Analysis SAPSummary
callTransfer finSumm callee actuals s (argIx, actual) = do
  argFin <- lookupArgumentSummaryList finSumm callee argIx
  -- Note that, for now, this setup assumes that functions finalizing
  -- their argument will not also write to a different field.  This
  -- assumption could be lifted if it becomes an issue.
  case PAFinalize `elem` argFin of
    False -> return $ fromMaybe s $ do
      calleeFunc <- fromValue callee
      calleeFormal <- functionParameters calleeFunc `at` argIx
      -- We now have to extend each of the summaries for this argument.
      -- Each summary tells us which other actual this formal is stored
      -- into.

      case valueContent' actual of
        -- This formal is @x@ in @f@; it is a *formal* argument passed
        -- to @g@ as an *actual* parameter.  'argumentTransfer'
        -- decides how to deal with the argument depending on the type
        -- of augmented access path that is in play.
        ArgumentC formal -> do
          let args = s ^. sapArguments
              fins = s ^. sapFinalize
              calleeFormalSumm = M.lookup calleeFormal args
              calleeFinalizeSumm = M.lookup calleeFormal fins
              args' = maybe args (F.foldr (augmentTransfer formal) args) calleeFormalSumm
              fins' = maybe fins (F.foldr (augmentTransferFinalize formal) fins) calleeFinalizeSumm
          return $ (sapFinalize .~ fins') $ (sapArguments .~ args') s
        -- Here, an instruction (from which we build an access path)
        -- is passed to a callee with a summary.  If that summary is a
        -- FinalizePath summary (we don't care about the case where a
        -- field of one argument is stored into the field of another),
        -- then we need to augment the FinalizePath.
        InstructionC actualInst -> do
          cap <- accessPath actualInst
          baseArg <- accessPathBaseArgument cap
          let absPath = abstractAccessPath cap
              fins = s ^. sapFinalize
              calleeFinalizeSumm = M.lookup calleeFormal fins
              fins' = maybe fins (F.foldr (finalizeTransfer baseArg absPath) fins) calleeFinalizeSumm
          return $ (sapFinalize .~ fins') s
        _ -> return s
    -- For this case (the actual argument is finalized), we only need
    -- to do something if
    --
    -- (1) we can construct an access path from the argument.  The
    --     case where an Argument is being finalized is handled in the
    --     finalizer analysis.
    --
    -- (2) The instruction argument is a Call that returns an access
    --     path.
    True -> return $ fromMaybe s $ do
      actualInst <- fromValue actual
      case actualInst of
        CallInst { callFunction = (valueContent' -> FunctionC argCallee)
                 , callArguments = (map fst -> riActuals)
                 } -> do
          retPaths <- M.lookup argCallee (s ^. sapReturns)
          return $ F.foldr (toFinalizedPath riActuals) s retPaths
        _ -> do
          cap <- accessPath actualInst
          baseArg <- accessPathBaseArgument cap
          let absPath = abstractAccessPath cap
              fp = FinalizePath absPath
          return $ (sapFinalize %~ M.insertWith S.union baseArg (S.singleton fp)) s
  where
    toFinalizedPath riActuals (ReturnPath ix p) fsumm =
      fromMaybe fsumm $ do
        mappedArg <- riActuals `at` ix
        pOrArg <- accessPathOrArgument mappedArg
        case pOrArg of
          -- This looks something like
          --
          -- > foo = funcReturningPath(a);
          -- > free(foo);
          --
          -- So the finalized path is just whatever is returned
          Left mappedArg' ->
            let fp = FinalizePath p
            in return $ (sapFinalize %~ M.insertWith S.union mappedArg' (S.singleton fp)) fsumm
          -- This case is more complicated:
          --
          -- > foo = funcReturningPath(a->baz);
          -- > free(foo);
          Right mappedPath -> do
            argBase <- accessPathBaseArgument mappedPath
            p' <- abstractAccessPath mappedPath `appendAccessPath` p
            let fp = FinalizePath p'
            return $ (sapFinalize %~ M.insertWith S.union argBase (S.singleton fp)) fsumm
    -- Extend finalized paths
    finalizeTransfer baseArg curPath (FinalizePath p) argSumm =
      fromMaybe argSumm $ do
        p' <- curPath `appendAccessPath` p
        let fp = FinalizePath p'
        return $ M.insertWith S.union baseArg (S.singleton fp) argSumm

    -- In this case, an argument is being passed directly to a callee
    -- that finalizes some argument of the field.  We just need to
    -- propagate the inferred annotation.
    augmentTransferFinalize formal fp@(FinalizePath _) argSumm =
      M.insertWith S.union formal (S.singleton fp) argSumm

    -- Called once per summary for this argument.  This is handling
    -- when an argument is stored into some access path of another
    -- argument.  This does not handle (and we do not care about)
    -- cases where a field of an argument is stored into a field of a
    -- different argument.
    augmentTransfer formal (WritePath dstArg p) argSumm =
      fromMaybe argSumm $ do
        baseActual <- actuals `at` dstArg
        case valueContent' baseActual of
          ArgumentC argActual -> do
            -- In this case, the actual argument is just an argument
            -- (could be considered a degenerate access path).  This
            -- is the case where an argument is passed-through to
            -- a function.
            --
            -- In the example, this would be the first argument to @g@
            -- if it was just an argument passed down to @g@ instead
            -- of a field access.
            let dstArg' = argumentIndex argActual
                wp = WritePath dstArg' p
            return $ M.insertWith S.union formal (S.singleton wp) argSumm
          _ -> do
            -- In this case, the actual argument is some field or
            -- array access.  That is @t->s@
            actualInst <- fromValue baseActual
            cap' <- accessPath actualInst
            -- @t@ in the example
            baseArg <- accessPathBaseArgument cap'
            let absPath = abstractAccessPath cap'
            -- Extend the summary from @g@ with the @t->s@ we just
            -- observed.
            p' <- absPath `appendAccessPath` p
            let dstArg' = argumentIndex baseArg
                wp = WritePath dstArg' p'
            return $ M.insertWith S.union formal (S.singleton wp) argSumm

-- | If this StoreInst represents the store of an Argument into a
-- field of another argument, record that in the sapArguments summary.
--
-- > void f(struct S *s, struct Foo *foo) {
-- >   s->bar = foo;
-- > }
--
-- > WritePath 0 S.<0> 1
--
-- Argument 1 is stored into field zero of argument 0.
storeTransfer :: SAPPTRelSummary
                 -> SAPSummary
                 -> Argument -- ^ The argument being stored
                 -> Analysis SAPSummary
storeTransfer ptrelSumm s storedArg =
  let ps = synthesizedPathsFor ptrelSumm storedArg
  in return $ addStore $ foldr toWritePath [] ps
  where
    addStore res' =
      (sapArguments %~ M.insertWith S.union storedArg (S.fromList res')) s
    toWritePath p acc = fromMaybe acc $ do
      base <- accessPathBaseArgument p
      let absPath = abstractAccessPath p
      return $! WritePath (argumentIndex base) absPath : acc


-- | When the result of a call is returned, that call is known to
-- return an access path *into* one of its arguments.  What we need to
-- do here is figure out which of the callee's arguments the access
-- path uses (the Int the AAP is tagged with).
--
-- We then take the actual argument at that index and look up its
-- access path.  If that concrete access path is rooted at an
-- argument, we get the index of that argument and then append the
-- access paths.
transitiveReturnTransfer :: Function
                            -> SAPSummary
                            -> Function
                            -> [Value]
                            -> Analysis SAPSummary
transitiveReturnTransfer f s@(SAPSummary rs _ _ _) callee args =
  return $ fromMaybe s $ do
    rpaths <- M.lookup callee rs
    let trpaths = mapMaybe extendRPath $ S.toList rpaths
        rs' = foldr (M.insertWith S.union f) rs trpaths
    return $ (sapReturns .~ rs') s
  where
    extendRPath (ReturnPath ix p) = do
      actual <- args `at` ix
      i <- fromValue actual
      cap <- accessPath i
      formal <- accessPathBaseArgument cap
      let absPath = abstractAccessPath cap
          tix = argumentIndex formal
      tp <- absPath `appendAccessPath` p
      return $ S.singleton (ReturnPath tix tp)

-- FIXME: This could actually probably work on external functions,
-- too, if we are careful in representing access paths
returnValueTransfer :: Function
                       -> SAPSummary
                       -> Instruction
                       -> Analysis SAPSummary
returnValueTransfer f s CallInst { callArguments = (map fst -> args)
                                 , callFunction = (valueContent' -> FunctionC callee) } =
  transitiveReturnTransfer f s callee args
returnValueTransfer f s InvokeInst { invokeArguments = (map fst -> args)
                                   , invokeFunction = (valueContent' -> FunctionC callee) } =
  transitiveReturnTransfer f s callee args
returnValueTransfer f s i = return $ fromMaybe s $ do
  p <- accessPath i
  let absPath = abstractAccessPath p
      addArg aid =
        let v = S.singleton $ ReturnPath aid absPath
        in (sapReturns %~ M.insertWith S.union f v) s
  a <- accessPathBaseArgument p
  return $ addArg (argumentIndex a)

-- Utilities

valuesAsInsts :: [Value] -> [Instruction]
valuesAsInsts = mapMaybe fromValue

accessPathBaseArgument :: AccessPath -> Maybe Argument
accessPathBaseArgument p =
  fromValue $ valueContent' (accessPathBaseValue p)

accessPathOrArgument :: Value -> Maybe (Either Argument AccessPath)
accessPathOrArgument v =
  case valueContent' v of
    ArgumentC a -> return (Left a)
    InstructionC i -> do
      cap <- accessPath i
      return (Right cap)
    _ -> Nothing


-- Testing

sapReturnResultToTestFormat :: SAPSummary -> Map String (Set (Int, String, [AccessType]))
sapReturnResultToTestFormat =
  M.fromList . map toTestFormat . M.toList . (^. sapReturns)
  where
    toTestFormat (f, s) =
      (identifierAsString (functionName f),
       S.map fromRetPath s)
    fromRetPath (ReturnPath ix p) =
      (ix, show (abstractAccessPathBaseType p),
       abstractAccessPathComponents p)

sapArgumentResultToTestFormat :: SAPSummary -> Map (String, String) (Set (Int, String, [AccessType]))
sapArgumentResultToTestFormat =
  M.fromList . map toTestFormat . M.toList . (^. sapArguments)
  where
    toTestFormat (a, s) =
      let f = argumentFunction a
          p1 = (identifierAsString (functionName f),
                identifierAsString (argumentName a))
      in (p1, S.map fromPath s)
    fromPath (WritePath ix p) =
      (ix, show (abstractAccessPathBaseType p),
       abstractAccessPathComponents p)

sapFinalizeResultToTestFormat :: SAPSummary -> Map (String, String) (Set (String, [AccessType]))
sapFinalizeResultToTestFormat =
  M.fromList . map toTestFormat . M.toList . (^. sapFinalize)
  where
    toTestFormat (a, s) =
      let f = argumentFunction a
          p1 = (identifierAsString (functionName f),
                identifierAsString (argumentName a))
      in (p1, S.map fromPath s)
    fromPath (FinalizePath p) =
      (show (abstractAccessPathBaseType p),
       abstractAccessPathComponents p)
