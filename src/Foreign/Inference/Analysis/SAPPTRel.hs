{-# LANGUAGE DeriveGeneric, TemplateHaskell, ViewPatterns #-}
{-# LANGUAGE RankNTypes, TypeSynonymInstances, FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
-- | This is an analysis to support the Symbolic Access Path (SAP)
-- analysis.  It computes, for every instruction, the PT (points-to)
-- relation from @conf\/cgo\/MatosevicA12@.  This information helps to
-- bridge the gap between standard symbolic access paths and shape
-- analysis.  Also note that the information in this PT relation
-- relates to /concrete/ access paths, rather than /abstract/ access
-- paths (as in SAP).  An example of what goes into the PT relation
-- (and why it is important) in terms of LLVM IR:
--
-- > define void @list_push(%struct.list_t* %lst, i8* %comp) nounwind uwtable {
-- > entry:
-- >   %call = call noalias i8* @malloc(i64 16) nounwind ; 0
-- >   %0 = bitcast i8* %call to %struct.list_elem_t*    ; 1
-- >   %head = getelementptr inbounds %struct.list_t* %lst, i32 0, i32 0    ; 2
-- >   %1 = load %struct.list_elem_t** %head, align 8    ; 3
-- >   %next = getelementptr inbounds %struct.list_elem_t* %0, i32 0, i32 1 ; 4
-- >   store %struct.list_elem_t* %1, %struct.list_elem_t** %next, align 8  ; 5
-- >   store %struct.list_elem_t* %0, %struct.list_elem_t** %head, align 8  ; 6
-- >   %data = getelementptr inbounds %struct.list_elem_t* %0, i32 0, i32 0 ; 7
-- >   store i8* %comp, i8** %data, align 8              ; 8
-- >   ret void                                          ; 9
-- > }
--
-- derived from the C snippet:
--
-- > void list_push(struct list_t *lst, void *comp) {
-- >   struct list_elem_t *e = malloc(sizeof(struct list_elem_t));
-- >   e->next = lst->head;
-- >   lst->head = e;
-- >   lst->head->data = comp;
-- > }
--
-- This analysis operates only on Store instructions, because they
-- introduce new points-to relations.  These points-to relations
-- technically let us equate points-to sets for concrete access paths.
--
-- (1) Instruction 5 gives us the relation @PT(e->next) = lst->head@.
--     That is, these two access paths point to the same set of values
--     (because of the assignment).
--
-- (2) Instruction 6 adds @PT(lst->head) = e@.
--
-- (3) Instruction 8 adds @PT(e->data) = comp@.
--
-- Individually, these facts are not very useful, but they do allow us
-- to infer that lst->head->data == comp by stringing together the
-- last two entries.
--
-- This gives us information in the SAP analysis that is not apparent
-- on its own: that @comp@ is stored, indirectly, into a field of
-- @lst@.
--
-- This analysis can be formulated as a forward dataflow analysis.
-- Within a basic block, the PT relation can be updated /strongly/
-- (overwriting existing bindings for a specific concrete access
-- path).  At control flow join points, the values from the different
-- incoming paths must be unioned together.  The SAP analysis will
-- only care about the analysis result at the exit instruction of each
-- function.
--
-- > @inproceedings{DBLP:conf/cgo/MatosevicA12,
-- >   author    = {Ivan Matosevic and
-- >                Tarek S. Abdelrahman},
-- >   title     = {Efficient bottom-up heap analysis for symbolic path-based
-- >                data access summaries},
-- >   booktitle = {CGO},
-- >   year      = {2012},
-- >   pages     = {252-263},
-- >   ee        = {http://doi.acm.org/10.1145/2259016.2259049},
-- >   crossref  = {DBLP:conf/cgo/2012},
-- >   bibsource = {DBLP, http://dblp.uni-trier.de}
-- > }
-- > @proceedings{DBLP:conf/cgo/2012,
-- >   editor    = {Carol Eidt and
-- >                Anne M. Holler and
-- >                Uma Srinivasan and
-- >                Saman P. Amarasinghe},
-- >   title     = {10th Annual IEEE/ACM International Symposium on Code Generation
-- >                and Optimization, CGO '12, San Jose, CA, USA - March 31
-- >                - April 04, 2012},
-- >   booktitle = {CGO},
-- >   publisher = {ACM},
-- >   year      = {2012},
-- >   isbn      = {978-1-4503-1206-6},
-- >   ee        = {http://dl.acm.org/citation.cfm?id=2259016},
-- >   bibsource = {DBLP, http://dblp.uni-trier.de}
-- > }
module Foreign.Inference.Analysis.SAPPTRel (
  SAPPTRelSummary,
  identifySAPPTRels,
  synthesizedPathsFor
  ) where

import GHC.Generics ( Generic )

import Control.DeepSeq
import Control.DeepSeq.Generics ( genericRnf )
import Control.Lens ( Simple, (%~), makeLenses )
import qualified Data.Foldable as F
import Data.Map ( Map )
import qualified Data.Map as M
import Data.Maybe ( fromMaybe, mapMaybe )
import Data.Monoid
import Data.Set ( Set )
import qualified Data.Set as S

import LLVM.Analysis
import LLVM.Analysis.AccessPath
import LLVM.Analysis.CFG
import LLVM.Analysis.CallGraphSCCTraversal
import LLVM.Analysis.Dataflow

import Foreign.Inference.AnalysisMonad
import Foreign.Inference.Diagnostics
import Foreign.Inference.Interface

data SAPPTRelSummary =
  SAPPTRelSummary { _sapPaths :: Map Function (Map AccessPath (Set AccessPath))
                  , _sapValues :: Map Function (Map Value (Set AccessPath))
                  , _sapDiagnostics :: Diagnostics
                  }
  deriving (Generic)

$(makeLenses ''SAPPTRelSummary)

data SAPInfo =
  SAPInfo { _sapInfoPaths :: Map AccessPath (Set AccessPath)
          , _sapInfoValues :: Map AccessPath (Set Value)
          }
  deriving (Eq, Show)

$(makeLenses ''SAPInfo)

instance Eq SAPPTRelSummary where
  (SAPPTRelSummary s1 v1 _) == (SAPPTRelSummary s2 v2 _) =
    s1 == s2 && v1 == v2

instance Monoid SAPPTRelSummary where
  mempty = SAPPTRelSummary mempty mempty mempty
  (SAPPTRelSummary s1 v1 d1) `mappend` (SAPPTRelSummary s2 v2 d2) =
    SAPPTRelSummary (M.union s1 s2) (M.union v1 v2) (d1 `mappend` d2)

instance NFData SAPPTRelSummary where
  rnf = genericRnf

instance HasDiagnostics SAPPTRelSummary where
  diagnosticLens = sapDiagnostics

instance SummarizeModule SAPPTRelSummary where
  summarizeFunction _ _ = []
  summarizeArgument _ _ = []

identifySAPPTRels :: (FuncLike funcLike, HasFunction funcLike, HasCFG funcLike)
                     => DependencySummary
                     -> Simple Lens compositeSummary SAPPTRelSummary
                     -> ComposableAnalysis compositeSummary funcLike
identifySAPPTRels ds =
  composableAnalysisM runner sapAnalysis
  where
    runner a = runAnalysis a ds () ()

instance MeetSemiLattice SAPInfo where
  meet (SAPInfo s1 v1) (SAPInfo s2 v2) =
    SAPInfo (M.unionWith S.union s1 s2) (M.unionWith S.union v1 v2)

instance BoundedMeetSemiLattice SAPInfo where
  top = SAPInfo mempty mempty

type Analysis = AnalysisMonad () ()

instance DataflowAnalysis Analysis SAPInfo where
  transfer = sapTransfer

sapAnalysis :: (FuncLike funcLike, HasFunction funcLike, HasCFG funcLike)
               => funcLike -> SAPPTRelSummary -> Analysis SAPPTRelSummary
sapAnalysis funcLike s = do
  funcInfo <- forwardDataflow top funcLike
  let exitInsts = functionExitInstructions f
      exitInfo = map (dataflowResult funcInfo) exitInsts
      SAPInfo ps vs = meets exitInfo
  return $! (sapValues %~ M.insert f (invertMap vs)) $ (sapPaths %~ M.insert f (invertMap ps)) s
  where
    f = getFunction funcLike

sapTransfer :: SAPInfo -> Instruction -> Analysis SAPInfo
sapTransfer s i =
  case i of
    StoreInst { storeAddress = (valueContent' -> InstructionC sai)
              , storeValue = sv } ->
      return $ fromMaybe s $ do
        -- We always need the path of the store address; stores to
        -- plain (non-access path) values aren't interesting here.
        destPath <- accessPath sai

        -- However, the RHS could be either a value or an access path.
        case valueAsAccessPath sv of
          Just storedPath ->
            let ins = M.insert destPath (S.singleton storedPath)
            in return $ (sapInfoPaths %~ ins) s
          Nothing ->
            let ins = M.insert destPath (S.singleton sv)
            in return $ (sapInfoValues %~ ins) s
    _ -> return s

valueAsAccessPath :: Value -> Maybe AccessPath
valueAsAccessPath v = fromValue v >>= accessPath

invertMap :: (Ord k, Ord v) => Map k (Set v) -> Map v (Set k)
invertMap = foldr doInvert mempty . M.toList
  where
    doInvert (k, vset) acc =
      F.foldr (\v a -> M.insertWith S.union v (S.singleton k) a) acc vset

appendConcretePath :: AccessPath -> AccessPath -> Maybe AccessPath
appendConcretePath (AccessPath b1 e1 p1) (AccessPath b2 e2 p2) =
  -- case valueType e1 == valueType b2 of
  --   False -> Nothing
  --   True ->
      Just $ AccessPath b1 e2 (p1 ++ p2)

-- | Enumerate the 'AccessPath's that an 'Argument' is stored into,
-- including 'AccessPath's synthesized from the PT relation.
synthesizedPathsFor :: SAPPTRelSummary -> Argument -> [AccessPath]
synthesizedPathsFor (SAPPTRelSummary p v _) a = fromMaybe [] $ do
  vs <- M.lookup f v
  ps <- M.lookup f p
  endValPaths <- M.lookup (toValue a) vs
  -- return () `debug` PP.pretty (S.toList endValPaths)
  -- return () `debug` PP.pretty (map (second S.toList) (M.toList vs))
  let maximalPaths = mapMaybe (extendPaths vs ps) (S.toList endValPaths)
  return $ concat maximalPaths
  where
    f = argumentFunction a
    extendPaths vs ps p0 = return $ fromMaybe [p0] $ do
      let base = accessPathBaseValue p0
      p' <- M.lookup base vs
      return $ concat $ mapMaybe (extendPath vs ps p0) (S.toList p')
    extendPath vs ps p0 p' = do
      ep <- p' `appendConcretePath` p0
      maybe (return [ep]) return (extendPaths vs ps ep)
