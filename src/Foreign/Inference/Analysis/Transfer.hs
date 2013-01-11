{-# LANGUAGE DeriveGeneric, TemplateHaskell, ViewPatterns #-}
{-# LANGUAGE RankNTypes #-}
-- | An analysis to identify interfaces that transfer ownership of objects.
--
-- The motivation for this analysis is that escape analysis is a poor
-- approximation of transfers.  Transfers are relatively rare:
--
-- @inproceedings{DBLP:conf/oopsla/MaF07,
--   author    = {Kin-Keung Ma and
--                Jeffrey S. Foster},
--   title     = {Inferring aliasing and encapsulation properties for java},
--   booktitle = {OOPSLA},
--   year      = {2007},
--   pages     = {423-440},
--   ee        = {http://doi.acm.org/10.1145/1297027.1297059},
--   crossref  = {DBLP:conf/oopsla/2007},
--   bibsource = {DBLP, http://dblp.uni-trier.de}
-- }
-- @proceedings{DBLP:conf/oopsla/2007,
--   editor    = {Richard P. Gabriel and
--                David F. Bacon and
--                Cristina Videira Lopes and
--                Guy L. Steele Jr.},
--   title     = {Proceedings of the 22nd Annual ACM SIGPLAN Conference on
--                Object-Oriented Programming, Systems, Languages, and Applications,
--                OOPSLA 2007, October 21-25, 2007, Montreal, Quebec, Canada},
--   booktitle = {OOPSLA},
--   publisher = {ACM},
--   year      = {2007},
--   isbn      = {978-1-59593-786-5},
--   bibsource = {DBLP, http://dblp.uni-trier.de}
-- }
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
import Control.Monad ( foldM, liftM )
import qualified Data.Foldable as F
import Data.Map ( Map )
import qualified Data.Map as M
import Data.Maybe ( fromMaybe )
import Data.Monoid
import Data.Set ( Set )
import qualified Data.Set as S

import LLVM.Analysis
import LLVM.Analysis.AccessPath
import LLVM.Analysis.CallGraph
import LLVM.Analysis.CallGraphSCCTraversal

import Foreign.Inference.AnalysisMonad
import Foreign.Inference.Diagnostics
import Foreign.Inference.Interface
import Foreign.Inference.Analysis.Finalize
import Foreign.Inference.Analysis.IndirectCallResolver
import Foreign.Inference.Analysis.Util.CalleeFold

import Debug.Trace
debug = flip trace

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
                     -> Simple Lens compositeSummary TransferSummary
                     -> compositeSummary
identifyTransfers funcLikes cg ds pta p1res flens tlens =
  (tlens .~ res) p1res
  where
    res = runAnalysis a ds () ()
    finSumm = p1res ^. flens
    trSumm = p1res ^. tlens
    -- The field ownership analysis doesn't need a fixed-point
    -- computation because it only depends on the finalizer analysis.
    --
    -- The parameter part does, though, because there is a transitive
    -- component of the analysis.
    ofields s = foldM (identifyOwnedFields cg pta finSumm) s funcLikes
    tparms s ownedFields = do
      s' <- foldM (identifyTransferredArguments pta ownedFields) s funcLikes
      case s' == s of
        True -> return s
        False -> tparms s' ownedFields
    a = ofields mempty >>= tparms trSumm

type Analysis = AnalysisMonad () ()

identifyTransferredArguments :: (HasFunction funcLike)
                                => IndirectCallSummary
                                -> Set AbstractAccessPath
                                -> TransferSummary
                                -> funcLike
                                -> Analysis TransferSummary
identifyTransferredArguments pta ownedFields trSumm flike =
  foldM checkTransfer trSumm (functionInstructions f)
  where
    f = getFunction flike
    formals = functionParameters f
    checkTransfer s i =
      case i of
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
          calleeArgumentFold argumentTransfer s pta callee args
        InvokeInst { invokeFunction = callee, invokeArguments = (map fst -> args) } ->
          calleeArgumentFold argumentTransfer s pta callee args
        _ -> return s

    argumentTransfer callee s (ix, (valueContent' -> ArgumentC arg)) = do
      annots <- lookupArgumentSummaryList s callee ix
      case PATransfer `elem` annots of
        False -> return s
        True -> return $ (transferArguments %~ S.insert arg) s
    argumentTransfer _ s _ = return s

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
      case valueContent' callee of
        FunctionC fn -> do
          let ixs = [0..length (functionParameters fn)]
          liftM or $ mapM (isFinalizerArg callee) ixs
        ExternalFunctionC ef -> do
          let ixs = [0..length (externalFunctionParameterTypes ef)]
          liftM or $ mapM (isFinalizerArg callee) ixs
        _ -> return False
    isFinalizerArg callee ix =
      liftM (elem PAFinalize) $ lookupArgumentSummaryList finSumm callee ix

-- | Add any field passed to a known finalizer to the accumulated Set.
--
-- This will eventually need to incorporate shape analysis results.
-- It will also need to distinguish somehow between fields that are
-- finalized and elements of container fields that are finalized.
identifyOwnedFields :: (HasFunction funcLike)
                       => CallGraph
                       -> IndirectCallSummary
                       -> FinalizerSummary
                       -> Set AbstractAccessPath
                       -> funcLike
                       -> Analysis (Set AbstractAccessPath)
identifyOwnedFields cg pta finSumm ownedFields funcLike = do
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
        False -> return acc
        True ->
          case valueContent' arg of
            InstructionC CallInst { callFunction = cf } -> undefined
            InstructionC i -> return $ fromMaybe acc $ do
              accPath <- accessPath i
              let absPath = abstractAccessPath accPath
              return $ S.insert absPath acc
            _ -> return acc

-- Starting from the arguments passed to finalizers, trace backwards
-- to construct an access path.  This is a top-down construction, but
-- should be reasonably efficient because we don't need to start at
-- very many places.
--
-- Maybe just use a recursive-descent kind of thing where actuals are
-- substituted for parameters...
--
-- Maybe modify the Finalizer analysis to note when the finalizer
-- *also* finalizes some owned fields.  This would let us build
-- finalized access paths bottom-up.  This would let us easily handle
-- a case like:
--
-- > freeChildren(a);
--
-- we could see that a->children->e is finalized, which would let us
-- know that anything stored to a->children->e is a transfer...

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
