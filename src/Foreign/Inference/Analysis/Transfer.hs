{-# LANGUAGE DeriveGeneric, TemplateHaskell, ViewPatterns #-}
{-# LANGUAGE RankNTypes #-}
-- | An analysis to identify interfaces that transfer ownership of objects.
--
-- The motivation for this analysis is that escape analysis is a poor
-- approximation of transfers.  Transfers are relatively rare:
--
-- > @inproceedings{DBLP:conf/oopsla/MaF07,
-- >   author    = {Kin-Keung Ma and
-- >                Jeffrey S. Foster},
-- >   title     = {Inferring aliasing and encapsulation properties for java},
-- >   booktitle = {OOPSLA},
-- >   year      = {2007},
-- >   pages     = {423-440},
-- >   ee        = {http://doi.acm.org/10.1145/1297027.1297059},
-- >   crossref  = {DBLP:conf/oopsla/2007},
-- >   bibsource = {DBLP, http://dblp.uni-trier.de}
-- > }
-- > @proceedings{DBLP:conf/oopsla/2007,
-- >   editor    = {Richard P. Gabriel and
-- >                David F. Bacon and
-- >                Cristina Videira Lopes and
-- >                Guy L. Steele Jr.},
-- >   title     = {Proceedings of the 22nd Annual ACM SIGPLAN Conference on
-- >                Object-Oriented Programming, Systems, Languages, and Applications,
-- >                OOPSLA 2007, October 21-25, 2007, Montreal, Quebec, Canada},
-- >   booktitle = {OOPSLA},
-- >   publisher = {ACM},
-- >   year      = {2007},
-- >   isbn      = {978-1-59593-786-5},
-- >   bibsource = {DBLP, http://dblp.uni-trier.de}
-- > }
module Foreign.Inference.Analysis.Transfer (
  TransferSummary,
  identifyTransfers,
  -- * Testing
  transferSummaryToTestFormat
  ) where

import GHC.Generics ( Generic )

import Control.DeepSeq
import Control.DeepSeq.Generics ( genericRnf )
import Control.Lens ( (%~), (.~), (^.), Simple, makeLenses )
import Control.Monad ( foldM, liftM, liftM2 )
import Control.Monad.Trans
import Control.Monad.Trans.Maybe
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
import LLVM.Analysis.CallGraph
import LLVM.Analysis.CallGraphSCCTraversal

import Foreign.Inference.AnalysisMonad
import Foreign.Inference.Diagnostics
import Foreign.Inference.Interface
import Foreign.Inference.Analysis.Finalize
import Foreign.Inference.Analysis.IndirectCallResolver
import Foreign.Inference.Analysis.SAP
import Foreign.Inference.Analysis.Util.CalleeFold

-- import qualified Text.PrettyPrint.GenericPretty as PP
-- import Debug.Trace
-- debug = flip trace

data TransferSummary = TransferSummary {
  _transferArguments :: Set Argument,
  _transferDiagnostics :: Diagnostics
  }
  deriving (Generic)

$(makeLenses ''TransferSummary)

instance Eq TransferSummary where
  (TransferSummary as1 _) == (TransferSummary as2 _) = as1 == as2

instance Monoid TransferSummary where
  mempty = TransferSummary mempty mempty
  mappend (TransferSummary t1 d1) (TransferSummary t2 d2) =
    TransferSummary (t1 `mappend` t2) (d1 `mappend` d2)

instance NFData TransferSummary where
   rnf = genericRnf

instance HasDiagnostics TransferSummary where
  diagnosticLens = transferDiagnostics

instance SummarizeModule TransferSummary where
  summarizeFunction _ _ = []
  summarizeArgument a (TransferSummary t _)
    | S.member a t = [(PATransfer, [])]
    | otherwise = []


-- Algorithm:
--
-- In one pass, determine all of the *structure fields* that are
-- passed to a finalizer.  These are *owned* fields.  The shape
-- analysis bit will come later (to find finalized things that are
-- stored in "container-likes")
--
-- Maybe we can remove the need for some shape analysis by looking at
-- dependence.
--
-- > void foo(bar * baz) {
-- >   while(hasNext(baz->quux)) {
-- >     q = next(&baz->quux);
-- >     free_quux(q);
-- >   }
-- > }
--
-- In a second pass, find all of the arguments that flow into those
-- owned fields and mark them as Transferred.  Again, this will need
-- to be aware of the pseudo-shape analysis results (i.e., this
-- parameter ends up linked into this data structure via this field
-- after this call).  This pass will need to reach a fixed point.
--
-- At the end of the day, this will be simpler than the escape
-- analysis since we do not need to track fields of arguments or
-- anything of that form.
--
-- This could additionally depend on the ref count analysis and just
-- strip off transfer tags from ref counted types.

identifyTransfers :: (HasFunction funcLike, Eq compositeSummary)
                     => [funcLike]
                     -> CallGraph
                     -> DependencySummary
                     -> IndirectCallSummary
                     -> compositeSummary
                     -> Simple Lens compositeSummary FinalizerSummary
                     -> Simple Lens compositeSummary SAPSummary
                     -> Simple Lens compositeSummary TransferSummary
                     -> compositeSummary
identifyTransfers funcLikes cg ds pta p1res flens slens tlens =
  (tlens .~ res) p1res
  where
    res = runAnalysis a ds () ()
    finSumm = p1res ^. flens
    trSumm = p1res ^. tlens
    sapSumm = p1res ^. slens
    -- The field ownership analysis doesn't need a fixed-point
    -- computation because it only depends on the finalizer analysis.
    --
    -- The parameter part does, though, because there is a transitive
    -- component of the analysis.
    ofields s = foldM (identifyOwnedFields cg pta finSumm sapSumm) s funcLikes
    tparms s ownedFields = do
      s' <- foldM (identifyTransferredArguments pta sapSumm ownedFields) s funcLikes
      case s' == s of
        True -> return s -- `debug` PP.pretty (S.toList ownedFields)
        False -> tparms s' ownedFields
    a = ofields mempty >>= tparms trSumm

type Analysis = AnalysisMonad () ()

identifyTransferredArguments :: (HasFunction funcLike)
                                => IndirectCallSummary
                                -> SAPSummary
                                -> Set AbstractAccessPath
                                -> TransferSummary
                                -> funcLike
                                -> Analysis TransferSummary
identifyTransferredArguments pta sapSumm ownedFields trSumm flike = do
  -- The preliminary pass with checkWrittenFormals uses the results of
  -- the SymbolicAccessPath analysis to resolve complex
  -- interprocedural field writes.  This includes container-like
  -- manipulations.
  trSumm' <- foldM checkWrittenFormals trSumm formals
  foldM checkTransfer trSumm' (functionInstructions f)
  where
    f = getFunction flike
    formals = functionParameters f
    checkWrittenFormals s formal =
      return $ fromMaybe s $ do
        wps <- writePaths formal sapSumm
        return $ foldr (checkWrittenFormal formal) s wps
    checkWrittenFormal formal (_, p) s =
      fromMaybe s $ do
        _ <- F.find (equivAccessPaths p) ownedFields
        return $ (transferArguments %~ S.insert formal) s

    checkTransfer s i =
      case i of
        -- This case handles simple transfers (where a function
        -- locally stores an argument into a field of another
        -- argument.  More complex cases are handled in
        -- checkWrittenFormals
        StoreInst { storeValue = (valueContent' -> ArgumentC sv) }
          | sv `elem` formals -> return $ fromMaybe s $ do
            -- We don't extract the storeAddress above because the
            -- access path construction handles that
            acp <- accessPath i
            let absPath = abstractAccessPath acp
            case S.member absPath ownedFields of
              True -> return $! (transferArguments %~ S.insert sv) s
              False -> return s
          | otherwise -> return s

        CallInst { callFunction = callee, callArguments = (map fst -> args) } ->
          calleeArgumentFold (argumentTransfer args) s pta callee args
        InvokeInst { invokeFunction = callee, invokeArguments = (map fst -> args) } ->
          calleeArgumentFold (argumentTransfer args) s pta callee args
        _ -> return s

    -- We only care about call arguments that are actually Arguments
    -- in the caller because field->field transfers are outside the
    -- scope of the analysis.
    argumentTransfer actuals callee s (ix, (valueContent' -> ArgumentC arg)) = do
      annots <- lookupArgumentSummaryList s callee ix
      case PATransfer `elem` annots of
        False ->
          -- In this case, the argument position isn't known to be a
          -- transfer argument.  We still have to check to see if the
          -- argument is written into a field of another argument that
          -- /is/ owned.
          --
          -- For each of the write paths we get here, find the index
          -- of the relevant target argument and look that up in
          -- @args@.  Extend the path to args if necessary and see if
          -- the result is owned.
          return $ fromMaybe s $ do
            wps <- writePaths arg sapSumm
            return $ foldr (checkWritePath actuals arg) s wps
        True -> return $ (transferArguments %~ S.insert arg) s
    argumentTransfer _ _ s _ = return s

    checkWritePath actuals writtenFormal (destArg, wp) s =
      fromMaybe s $ do
        let destIx = argumentIndex destArg
        actualDst <- actuals `at` destIx
        extension <- accessPathOrArgument actualDst
        case extension of
          Left _ -> do
            _ <- F.find (equivAccessPaths wp) ownedFields
            return $ (transferArguments %~ S.insert writtenFormal) s
          Right cap -> do
            -- Ensure the base of the access path is an Argument
            _ <- accessPathBaseArgument cap
            let absPath = abstractAccessPath cap
            extendedPath <- absPath `appendAccessPath` wp
            _ <- F.find (equivAccessPaths extendedPath) ownedFields
            return $ (transferArguments %~ S.insert writtenFormal) s

-- | Determine whether or not the given function is a finalizer.  We
-- need this because we only want to infer ownership from finalizer
-- calls *within another finalizer*.
--
-- This lets us ignore almost all "local" deletes where some
-- locally-allocated value is stored in a struct and then finalized.
isFinalizerContext :: (HasFunction funcLike)
                      => CallGraph
                      -> FinalizerSummary
                      -> funcLike
                      -> Analysis Bool
isFinalizerContext cg finSumm flike =
  liftM or $ mapM isFinalizer callers
  where
    f = getFunction flike
    callers = allFunctionCallers cg f
    isFinalizer callee =
      liftM2 fromMaybe (return False) $ runMaybeT (checkFinCtx callee)
    checkFinCtx callee = do
      nargs <- formalArgumentCount callee
      liftM or $ mapM (isFinalizerArg callee) [0..nargs]
    isFinalizerArg callee ix =
      liftM (elem PAFinalize) $ lift $ lookupArgumentSummaryList finSumm callee ix

formalArgumentCount :: Value -> MaybeT Analysis Int
formalArgumentCount v =
  case valueContent' v of
    FunctionC fn -> return $ length $ functionParameters fn
    ExternalFunctionC ef -> return $ length $ externalFunctionParameterTypes ef
    _ -> fail "Not a function"

-- | Add any field passed to a known finalizer to the accumulated Set.
--
-- This will eventually need to incorporate shape analysis results.
-- It will also need to distinguish somehow between fields that are
-- finalized and elements of container fields that are finalized.
identifyOwnedFields :: (HasFunction funcLike)
                       => CallGraph
                       -> IndirectCallSummary
                       -> FinalizerSummary
                       -> SAPSummary
                       -> Set AbstractAccessPath
                       -> funcLike
                       -> Analysis (Set AbstractAccessPath)
identifyOwnedFields cg pta finSumm sapSumm ownedFields funcLike = do
  isFin <- isFinalizerContext cg finSumm funcLike
  case isFin of
    True -> foldM checkFinalize ownedFields insts
    False -> return ownedFields
  where
    insts = functionInstructions (getFunction funcLike)
    checkFinalize acc i =
      case i of
        CallInst { callFunction = cf, callArguments = (map fst -> args) } ->
          calleeArgumentFold addFieldIfFinalized acc pta cf args
        InvokeInst { invokeFunction = cf, invokeArguments = (map fst -> args) } ->
          calleeArgumentFold addFieldIfFinalized acc pta cf args
        _ -> return acc

    addFieldIfFinalized target acc (ix, arg) = do
      annots <- lookupArgumentSummaryList finSumm target ix
      case PAFinalize `elem` annots of
        -- In this case we aren't seeing a known finalizer call;
        -- instead, check to see if the call is known to finalize some
        -- field of one of its arguments.
        False -> return $ fromMaybe acc $ do
          calleeArg <- calleeFormalAt target ix
          ffs <- finalizedPaths calleeArg sapSumm
          case valueContent' arg of
            ArgumentC _ ->
              -- All of the paths described by ffs are owned fields,
              -- so union them with acc.  We don't need the ArgumentC
              -- binding here; it is only to let us know that this
              -- actual is really a formal in the current function and
              -- we need to propagate information about it upwards in
              -- the summary.
              return $ acc `S.union` S.fromList ffs
            InstructionC i -> do
              -- We don't need the base argument, we just need to know
              -- that the base is an Argument.
              (cap, _) <- anyArgumentAccessPath i
              let absPath = abstractAccessPath cap
                  extended = mapMaybe (appendAccessPath absPath) ffs
              -- Extend absPath by each of the paths described in ffs.
              -- These are *all* owned fields:
              return $ acc `S.union` S.fromList extended
            _ -> Nothing
        -- Calling a known finalizer on some value
        True ->
          case valueContent' arg of
            -- Calling a finalizer on the result of a function call.
            -- Here, we need to look up the function summary of cf and
            -- see if it is returning some access path of one of its
            -- actual arguments.
            InstructionC CallInst { callFunction = (valueContent' -> FunctionC cf)
                                  , callArguments = (map fst -> args)
                                  } ->
              return $ fromMaybe acc $ do
                calleeArg <- calleeFormalAt cf ix
                rps <- returnedPaths cf calleeArg sapSumm
                -- These paths (from @calleeArg@) are returned.  We
                -- have to extend each path with the actual argument
                -- passed in that position.
                actualAtIx <- args `at` argumentIndex calleeArg
                pathOrArg <- accessPathOrArgument actualAtIx
                case pathOrArg of
                  Left _ ->
                    return $ acc `S.union` S.fromList rps
                  Right p ->
                    let absPath = abstractAccessPath p
                        rps' = mapMaybe (appendAccessPath absPath) rps
                    in return $ acc `S.union` S.fromList rps'
            -- Calling a finalizer on a local access path
            InstructionC i -> return $ fromMaybe acc $ do
              accPath <- accessPath i
              let absPath = abstractAccessPath accPath
              return $ S.insert absPath acc
            _ -> return acc

calleeFormalAt :: (IsValue v) => v -> Int -> Maybe Argument
calleeFormalAt target ix = do
  callee <- fromValue (toValue target)
  let params = functionParameters callee
  params `at` ix

accessPathBaseArgument :: AccessPath -> Maybe Argument
accessPathBaseArgument p =
  fromValue $ valueContent' (accessPathBaseValue p)

-- The end type does not always match up for various unimportant
-- reasons.  All that really matters is that the base types and path
-- components match.  It might be worth pushing this down to the
-- AccessPath Eq instance, but I don't know what effect that will have
-- on the derived Ord instance.
equivAccessPaths :: AbstractAccessPath -> AbstractAccessPath -> Bool
equivAccessPaths (AbstractAccessPath bt1 _ c1) (AbstractAccessPath bt2 _ c2) =
  bt1 == bt2 && c1' == c2'
  where
    c1' = filter (/=AccessDeref) $ map snd c1
    c2' = filter (/=AccessDeref) $ map snd c2

-- Testing


transferSummaryToTestFormat :: TransferSummary -> Map String (Set String)
transferSummaryToTestFormat (TransferSummary s _) =
  F.foldr convert mempty s
  where
    convert a m =
      let f = argumentFunction a
          k = show (functionName f)
          v = show (argumentName a)
      in M.insertWith S.union k (S.singleton v) m
