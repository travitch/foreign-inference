{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE OverloadedStrings, FlexibleContexts, RankNTypes #-}
{-# LANGUAGE DeriveGeneric, TemplateHaskell #-}
module Foreign.Inference.Analysis.Escape (
  EscapeSummary,
  identifyEscapes,
  instructionEscapes,
  instructionEscapesWith,

  -- * Testing
  EscapeClass(..),
  escapeResultToTestFormat,
  escapeUseGraphs,
  useGraphvizRepr
  ) where

import GHC.Generics ( Generic )

import Control.Arrow
import Control.DeepSeq
import Control.DeepSeq.Generics ( genericRnf )
import Control.Lens ( Simple, (^.), (%=), (%~), (.~), use, makeLenses )
import Control.Monad.State.Strict
import Control.Monad.Writer ( runWriter )
import Data.GraphViz
import Data.Hashable
import Data.HashMap.Strict ( HashMap )
import qualified Data.HashMap.Strict as HM
import Data.List ( find, partition, transpose )
import Data.List.NonEmpty ( NonEmpty, nonEmpty )
import qualified Data.List.NonEmpty as NEL
import Data.Map ( Map )
import qualified Data.Map as M
import Data.Maybe ( fromMaybe, mapMaybe )
import Data.Set ( Set )
import qualified Data.Set as S
import Data.Monoid
import Text.Printf

import Data.Graph.Interface
import Data.Graph.LazyHAMT
import Data.Graph.Algorithms.Matching.DFS

import LLVM.Analysis
import LLVM.Analysis.AccessPath
import LLVM.Analysis.CallGraphSCCTraversal

import Foreign.Inference.Diagnostics ( HasDiagnostics(..), Diagnostics )
import Foreign.Inference.Interface
import Foreign.Inference.Analysis.IndirectCallResolver

import System.IO.Unsafe
-- import Text.Printf
-- import Debug.Trace
-- debug = flip trace

-- | The ways a value can escape from a function
data EscapeClass = DirectEscape
                 | BrokenContractEscape
                 | IndirectEscape
                 | ArgumentEscape !Int -- ^ Index escaped into
                 deriving (Eq, Ord, Read, Show)

instance Hashable EscapeClass where
  hash DirectEscape = 76
  hash BrokenContractEscape = 699
  hash IndirectEscape = 5
  hash (ArgumentEscape i) = 77997 `combine` hash i

instance NFData EscapeClass

data ArgumentDescriptor = ArgumentDescriptor Function Int
                        deriving (Eq, Ord, Show, Generic)

instance NFData ArgumentDescriptor where
  rnf = genericRnf

-- | The node labels for the Value Flow Graph
data ValueFlowNode = Sink { sinkClass :: EscapeClass
                          , sinkWitness :: Instruction
                          , sinkIntoArgument :: Maybe ArgumentDescriptor
                          }
                   | Location { locationValue :: Value }
                   | FieldSource { fieldSourceArgument :: Argument
                                 , fieldSourcePath :: AbstractAccessPath
                                 }
                   | AllocaSink EscapeClass Instruction Instruction
                   deriving (Eq, Ord, Show, Generic)

instance Labellable ValueFlowNode where
  toLabelValue (Sink c i _) =
    let s :: String
        s = printf "%s(%s)" (show i) (show c)
    in toLabelValue s
  toLabelValue (Location v) = toLabelValue (show v)
  toLabelValue (FieldSource a p) =
    let s :: String
        s = printf "%s -> %s" (show a) (show p)
    in toLabelValue s
  toLabelValue (AllocaSink c ai w) =
    let s :: String
        s = printf "%s(%s)" (show ai) (show c)
    in toLabelValue s

instance NFData ValueFlowNode where
  rnf = genericRnf

data ValueFlowEdge = UnconditionalEdge
                   | ForwardEdge
                   | BackwardEdge
                   deriving (Eq, Ord, Show)

instance NFData ValueFlowEdge

type ValueFlowGraph = Gr ValueFlowNode ValueFlowEdge

-- Rules:
--
-- Each value gets a single node.  Nodes can be created from any
-- location.
--
-- Field source nodes are only created by the fieldSource function.
-- These are load instructions and arguments that are proxied to
-- function calls that let an argument escape.  There can be more than
-- one for a given value (because of the second condition).  The
-- important thing is that, after all other nodes are created, each
-- field source @fs@ has value root @v@.  For all edges @v@->@x@, add
-- new edg @fs@->@x@.
data GraphState = GraphState {
  _graphStateValueMap :: HashMap Value (LNode ValueFlowGraph),
  -- ^ A map of values to their representative nodes
  _graphStateFieldSourceMap :: HashMap Value [LNode ValueFlowGraph],
  -- ^ A map of values that act as field sources to their graph nodes.
  _graphStateEdges :: HashMap Int [LEdge ValueFlowGraph],
  -- ^ All of the edges, mapped from their srcid.  This is useful
  -- because we need to be able to get all edges rooted at a node to
  -- deal with fieldSources
  _graphStateSinks :: [LNode ValueFlowGraph],
  -- ^ All of the sink nodes generated
  _graphStateFieldStores :: HashMap Value [(AbstractAccessPath, Int, Instruction)],
  -- ^ A map of base values to which the mapped value is stored into
  -- the associated path by an instruction.  These are corroborated
  -- with callFieldEscapes.
  _graphStateCallFieldEscapes :: HashMap Value [(AbstractAccessPath, Int)],
  -- ^ A map of values passed to call arguments that let a field
  -- escape to the sink nodes representing those escapes.  It is
  -- annotated with the field that it allows to escape so that can be
  -- compared with the path in the fieldStores.
  _graphStateIdSrc :: Int
  -- ^ A source of unique identifiers for graph nodes
  }

$(makeLenses ''GraphState)

emptyGraphState :: GraphState
emptyGraphState = GraphState { _graphStateValueMap = mempty
                             , _graphStateFieldSourceMap = mempty
                             , _graphStateEdges = mempty
                             , _graphStateSinks = mempty
                             , _graphStateFieldStores = mempty
                             , _graphStateCallFieldEscapes = mempty
                             , _graphStateIdSrc = 0
                             }

instance (Eq a, Eq b, Ord a, Ord b) => Eq (Gr a b) where
  (==) = graphEqual

data EscapeGraph = EscapeGraph {
  _escapeGraphValueMap :: HashMap Value (LNode ValueFlowGraph),
  _escapeGraphFieldSourceMap :: HashMap Value [LNode ValueFlowGraph],
  _escapeVFG :: ValueFlowGraph
  } deriving (Eq, Generic)

instance NFData EscapeGraph where
  rnf = genericRnf

$(makeLenses ''EscapeGraph)

-- | The monad in which we construct the value flow graph
type GraphBuilder = State GraphState

data EscapeSummary =
  EscapeSummary { _escapeGraph :: HashMap Function EscapeGraph
                , _escapeArguments :: HashMap Argument (EscapeClass, Instruction)
                , _escapeFields :: HashMap Argument (Set (EscapeClass, AbstractAccessPath, Instruction))
                , _escapeIntoArguments :: HashMap Argument (EscapeClass, Function, Int)
                , _escapeDiagnostics :: Diagnostics
                }
  deriving (Generic)

$(makeLenses ''EscapeSummary)

instance Show EscapeSummary where
  show (EscapeSummary _ ea ef ei _) = show ea ++ "/" ++ show ef ++ "/" ++ show ei

instance Eq EscapeSummary where
  (EscapeSummary g1 ea1 ef1 ei1 _) == (EscapeSummary g2 ea2 ef2 ei2 _) =
    g1 == g2 && ea1 == ea2 && ef1 == ef2 && ei1 == ei2

emptySummary :: EscapeSummary
emptySummary = EscapeSummary mempty mempty mempty mempty mempty

instance Monoid EscapeSummary where
  mempty = emptySummary
  mappend (EscapeSummary g1 as1 was1 ei1 d1) (EscapeSummary g2 as2 was2 ei2 d2) =
    EscapeSummary { _escapeGraph = HM.union g1 g2
                  , _escapeArguments = HM.union as1 as2
                  , _escapeFields = HM.union was1 was2
                  , _escapeIntoArguments = HM.union ei1 ei2
                  , _escapeDiagnostics = d1 `mappend` d2
                  }

instance NFData EscapeSummary where
  rnf = genericRnf

instance HasDiagnostics EscapeSummary where
  diagnosticLens = escapeDiagnostics

instance SummarizeModule EscapeSummary where
  summarizeFunction _ _ = []
  summarizeArgument = summarizeEscapeArgument

-- | This is the underlying bottom-up analysis to identify which
-- arguments escape.  It builds an EscapeGraph for the function
-- (incorporating information from other functions that have already
-- been analyzed) and then checks to see which arguments escape using
-- that graph.
identifyEscapes :: (FuncLike funcLike, HasFunction funcLike)
                   => DependencySummary
                   -> IndirectCallSummary
                   -> Simple Lens compositeSummary EscapeSummary
                   -> ComposableAnalysis compositeSummary funcLike
identifyEscapes ds ics lns =
  composableAnalysisM runner escapeWrapper lns
  where
    escapeWrapper funcLike s = do
      let f = getFunction funcLike
          g = buildValueFlowGraph ics ds s (functionInstructions f)
          s' = foldr (summarizeArgumentEscapes g) s (functionParameters f)
      return $ (escapeGraph %~ HM.insert f g) s'

    runner a =
      let (e, diags) = runWriter a
      in (escapeDiagnostics .~ diags) e
{-
    extSumm ef ix =
      -- FIXME: Switch the builder to be a StateT so we can let this
      -- monadic extsumm record missing summaries
      case lookupArgumentSummary ds (undefined :: EscapeSummary) ef ix of
        Nothing -> True --  do
          -- let msg = "Missing summary for " ++ show (externalFunctionName ef)
          -- emitWarning Nothing "EscapeAnalysis" msg
          -- return True
        Just annots -> PAEscape `elem` annots
-}

-- | A generalization of 'instructionEscapes'.  The first argument is
-- a predicate that returns True if the input Instruction (which is a
-- sink) should be excluded from the reachability search of the value
-- flow graph.
--
-- The intended use of this variant is to issue escape queries for
-- instructions that are known to escape via some desired means (e.g.,
-- an out parameter) and to determine if they also escape via some
-- other means.  In that case, the @ignore@ predicate should return
-- True for the store instruction that created the known escape.
instructionEscapesWith :: (Instruction -> Bool)
                          -> Instruction
                          -> EscapeSummary
                          -> Maybe Instruction
instructionEscapesWith = instructionEscapeCore

-- | Returns the instruction (if any) that causes the input
-- instruction to escape.  This does *not* cover WillEscape at all.
instructionEscapes :: Instruction -> EscapeSummary -> Maybe Instruction
instructionEscapes = instructionEscapeCore (const False)

-- | This is shared code for all of the instruction escape queries.
--
-- Most of the description is on 'instructionEscapesWith'
instructionEscapeCore :: (Instruction -> Bool)
                         -> Instruction
                         -> EscapeSummary
                         -> Maybe Instruction
instructionEscapeCore ignorePred i (EscapeSummary egs _ _ _ _) = do
  ln <- HM.lookup (toValue i) m
  let reached = reachableSinks eg (unlabelNode ln) g ignorePred
  case filter (not . allocaSink) reached of
    [] -> Nothing
    (Sink _ w _) : _ -> return w
    _ -> error "Non-sink in reachableSinks result 1"
  where
    Just f = instructionFunction i
    errMsg = error ("Missing summary for function " ++ show (functionName f))
    eg@(EscapeGraph m _ g) = HM.lookupDefault errMsg f egs

summarizeEscapeArgument :: Argument -> EscapeSummary -> [(ParamAnnotation, [Witness])]
summarizeEscapeArgument a er =
  case HM.lookup a (er ^. escapeArguments) of
    Nothing -> []
    Just (DirectEscape, w@RetInst {}) -> [(PAWillEscape, [Witness w "ret"])]
    Just (t, w@StoreInst {}) -> [(tagToAnnot t, [Witness w "store"])]
    Just (t, w@CallInst {}) -> [(tagToAnnot t, [Witness w "call"])]
    Just (t, w@InvokeInst {}) -> [(tagToAnnot t, [Witness w "call"])]
    Just (t, w) -> [(tagToAnnot t, [Witness w "access"])]
  where
    tagToAnnot t =
      case t of
        DirectEscape -> PAEscape
        IndirectEscape -> PAFptrEscape
        BrokenContractEscape -> PAContractEscape
        ArgumentEscape ix -> PAArgEscape ix

summarizeArgumentEscapes :: EscapeGraph -> Argument -> EscapeSummary -> EscapeSummary
summarizeArgumentEscapes eg a s =
  case entireArgumentEscapes eg a s of
    (True, s') -> s'
    (False, s') -> argumentFieldsEscape eg a s'

-- | This is basically DFS.  It is parameterized by a predicate that
-- returns True if the Instruction labelling a sink (and its
-- associated sink) should be ignored.  This is needed for
-- instructionEscapesWith (so we can say "this instruction escapes
-- ignoring this other instruction").
--
-- Also note that for any reachable store, a follow up query must be
-- issued to see if any sinks are reachable following store edges
-- (once that functionality is implemented).  Be sure to remember
-- stores that have been processed so that it doesn't loop forever.
-- The recursive traversals should occur here so that clients only
-- need to look for sinks.
reachableSinks :: EscapeGraph -> Int -> ValueFlowGraph -> (Instruction -> Bool) -> [ValueFlowNode]
reachableSinks eg nodeId g ignoredPred =
  let topReached = doReach False nodeId g
      reachedStores = mapMaybe isStoreNode topReached
      backReached = findBackReached mempty reachedStores []
  in filter isSinkNode (unique (topReached ++ backReached))
  where
    findBackReached _ [] reached = reached
    findBackReached visited (nid:rest) reached =
      case nid `S.member` visited of
        False ->
          let rs = doReach True nid g
          in findBackReached (S.insert nid visited) rest (rs ++ reached)
        True -> findBackReached visited rest reached
    unique = S.toList . S.fromList
    isStoreNode (Location v) =
      case valueContent' v of
        InstructionC StoreInst { storeAddress = sa } ->
          fmap unlabelNode $ HM.lookup sa (eg ^. escapeGraphValueMap)
        _ -> Nothing
    isStoreNode _ = Nothing
    isSinkNode (Sink _ _ _) = True
    isSinkNode (AllocaSink _ _ _) = True
    isSinkNode _ = False
    doReach followBackedge nid =
      xdfsWith (contextNeighbors followBackedge) contextToReached [nid]
    contextNeighbors followBackedge c =
      mapMaybe (sinkWitnessNotIgnored followBackedge) (lsuc' c)
    sinkWitnessNotIgnored followBackedge (nid, e) =
      case (followBackedge, e) of
        (False, BackwardEdge) -> Nothing
        _ ->
          case lab g nid of
            Nothing -> error "Missing label in reachableSinks"
            Just (Sink _ w _) ->
              case not (ignoredPred w) of
                True -> Just nid
                False -> Nothing
            _ -> Just nid
    contextToReached (Context _ (LNode _ l) _) = l

allocaSink :: ValueFlowNode -> Bool
allocaSink (AllocaSink _ _ _) = True
allocaSink _ = False

entireArgumentEscapes :: EscapeGraph -> Argument -> EscapeSummary -> (Bool, EscapeSummary)
entireArgumentEscapes eg a s =
  case HM.lookup (toValue a) (eg ^. escapeGraphValueMap) of
    Nothing -> (False, s)
    Just (LNode nid _) ->
      let reached = reachableSinks eg nid (eg ^. escapeVFG) (const False)
      in case partition allocaSink reached of
        -- No non-field escapes, so signal the caller to try to check
        -- for those.
        ([], []) -> (False, s)
        (allocaSinks, []) ->
          case find allocaSinkEscapes allocaSinks of
            -- No edges from the alloca reach a sink, so it does not
            -- escape and the values that "escape" into it also do not
            -- escape.
            Nothing -> (True, s)
            Just (AllocaSink eclass _ w) ->
              (True, (escapeArguments %~ HM.insert a (DirectEscape, w)) s)
            _ -> error "Non-alloca sink in the allocaSinks list"
        -- The argument escapes (ONLY) into another argument.  We need
        -- to record this to propagate the information to the caller.
        (_, [Sink eclass w (Just (ArgumentDescriptor f ix))]) ->
          (False, (escapeIntoArguments %~ HM.insert a (eclass, f, ix)) s)
        -- Otherwise, this argument escapes normally.  Just take the
        -- first one for now (we could record them all...)
        (_, (Sink eclass w _):_) ->
          (True, (escapeArguments %~ HM.insert a (eclass, w)) s)
        (_, _) -> error "entireArgumentEscapes: Non-sink in sink list"
  where
    -- | If at least one of the alloca sinks can reach another sink,
    -- the value escapes normally.
    allocaSinkEscapes (AllocaSink _ allocaInst _) =
      case HM.lookup (toValue allocaInst) (eg ^. escapeGraphValueMap) of
        -- No edges to or from the alloca inst
        Nothing -> False
        Just (LNode aid _) ->
          case reachableSinks eg aid (eg ^. escapeVFG) (const False) of
            [] -> False
            _ -> True
    allocaSinkEscapes _ = error "allocaSinkEscapes: Non AllocaSink in alloca sinks list"

argumentFieldsEscape :: EscapeGraph -> Argument -> EscapeSummary -> EscapeSummary
argumentFieldsEscape eg a s =
  case HM.lookup (toValue a) (eg ^. escapeGraphFieldSourceMap) of
    -- No fields escape either
    Nothing -> s
    Just fieldSrcs -> foldr checkFieldEscapes s fieldSrcs
  where
    checkFieldEscapes (LNode fldSrcId (FieldSource arg p)) summ =
      let reached = reachableSinks eg fldSrcId (eg ^. escapeVFG) (const False)
      in case filter (not . allocaSink) reached of
        [] -> summ
        (Sink eclass w _) : _ ->
          let newEsc = S.singleton (eclass, p, w)
          in (escapeFields %~ HM.insertWith S.union arg newEsc) summ
        _ -> error "Non-sink found in reachableSinks result 3"
    checkFieldEscapes _ _ = error "argumentFieldsEscape: Non FieldSource in fieldSrcs list"

isSink :: Maybe Value -> Maybe Value
isSink v = do
  v' <- v
  case valueContent' v' of
    ArgumentC _ -> Just v'
    GlobalVariableC _ -> Just v'
    ExternalValueC _ -> Just v'
    InstructionC (CallInst {}) -> Just v'
    InstructionC (InvokeInst {}) -> Just v'
    _ -> Nothing

-- | A helper to abstract the pointer type tests.  If the value @v@ is
-- not a pointer, return @defVal@.  Otherwise, return @isPtrVal@.
-- This helps remove a level of nested (and repetitive) pattern
-- matching.
ifPointer :: IsValue v => v -> a -> a -> a
ifPointer v defVal isPtrVal =
  case valueType v of
    TypePointer _ _ -> isPtrVal
    _ -> defVal

dumpGraph :: ValueFlowGraph -> ValueFlowGraph
dumpGraph g = unsafePerformIO $ do
  let dg = useGraphvizRepr g
  runGraphvizCanvas' dg Gtk
  return g

buildValueFlowGraph :: IndirectCallSummary
                       -> DependencySummary -- (ExternalFunction -> Int -> Bool)
                       -> EscapeSummary
                       -> [Instruction]
                       -> EscapeGraph
buildValueFlowGraph ics ds summ is =
  EscapeGraph { _escapeGraphValueMap = sN ^. graphStateValueMap
              , _escapeGraphFieldSourceMap = sN ^. graphStateFieldSourceMap
              , _escapeVFG = {- dumpGraph $ -} mkGraph ns es
              }
  where
    ns = concat [ HM.elems (sN ^. graphStateValueMap)
                , concat $ HM.elems (sN ^. graphStateFieldSourceMap)
                , sN ^. graphStateSinks
                ]
    es = concat [ callFieldEdges
                , fieldSourceEdges
                , concat $ HM.elems (sN ^. graphStateEdges)
                ]

    sN = execState b emptyGraphState
    b = mapM_ (addFact ics ds summ) is
    fieldSourceEdges = concatMap (addFieldSourceEdges sN) (HM.toList (sN ^. graphStateFieldSourceMap))
    callFieldEdges = concatMap (addCallFieldEdges sN) (HM.toList (sN ^. graphStateCallFieldEscapes))

addCallFieldEdges :: GraphState
                     -> (Value, [(AbstractAccessPath, Int)])
                     -> [LEdge ValueFlowGraph]
addCallFieldEdges gs (base, sinkPaths) =
  fromMaybe [] $ do
    fsnodes <- HM.lookup base (gs ^. graphStateFieldStores)
    return $ concatMap (makeEdges fsnodes) sinkPaths
  where
    makeEdges fsnodes (p, dest) = mapMaybe (makeEdge p dest) fsnodes
    makeEdge p1 dest (p2, src, _)
      | p1 == p2 = Nothing
      | otherwise = return $ LEdge (Edge src dest) UnconditionalEdge

-- | For each fieldSource node, find all of the normal nodes with the
-- same base.  For each of those nodes, clone their edges and replace
-- the source with this fieldsource node.  Note, it is possible that
-- there are simply none to add.
addFieldSourceEdges :: GraphState
                       -> (Value, [LNode ValueFlowGraph])
                       -> [LEdge ValueFlowGraph]
addFieldSourceEdges gs (base, fsnodes) =
  fromMaybe [] $ do
    normalNode <- HM.lookup base (gs ^. graphStateValueMap)
    es <- HM.lookup (unlabelNode normalNode) (gs ^. graphStateEdges)
    return $ concatMap (convertEdges es) fsnodes
  where
    convertEdge src (LEdge (Edge _ dst) lbl) = LEdge (Edge src dst) lbl
    convertEdges es n = map (convertEdge (unlabelNode n)) es

nextNodeId :: GraphBuilder Int
nextNodeId = do
  nid <- use graphStateIdSrc
  _ <- graphStateIdSrc %= (+1)
  return nid

-- | Create a node for the given value if it does not already exist.
-- Returns the corresponding unique node id.
valueNode :: Value -> GraphBuilder Int
valueNode v = do
  vm <- use graphStateValueMap
  case HM.lookup v vm of
    Just n -> return (unlabelNode n)
    Nothing -> do
      nid <- nextNodeId
      let n = LNode nid (Location v)
      _ <- graphStateValueMap %= HM.insert v n
      return nid

-- | Values flow from v1 to v2
flowTo :: Value -> Value -> Instruction -> ValueFlowEdge -> GraphBuilder ()
flowTo from to w etype = do
  fromN <- valueNode from
  toN <- valueNode to
  let e = LEdge (Edge fromN toN) etype
  _ <- graphStateEdges %= HM.insertWith (++) fromN [e]
  return ()

-- | The value named flows to a sink.  This should create a new node
-- (each sink is accompanied by a flowTo).  Having it make a new node
-- allows us to have each argument be a sink without requiring fancy
-- handling of arguments (seeing if they are in a loop, &c)
flowToSink :: EscapeClass -> Value -> Instruction -> Maybe ArgumentDescriptor -> GraphBuilder ()
flowToSink eclass v w ad = do
  -- The value node
  vN <- valueNode v
  -- A virtual node representing the sink
  sid <- nextNodeId
  let s = LNode sid (Sink eclass w ad)
      e = LEdge (Edge vN sid) UnconditionalEdge
  _ <- graphStateEdges %= HM.insertWith (++) vN [e]
  _ <- graphStateSinks %= (s:)
  return ()

flowToAlloca :: EscapeClass -> Value -> Instruction -> Instruction -> GraphBuilder ()
flowToAlloca eclass arg i w = do
  vN <- valueNode arg
  sid <- nextNodeId
  let s = LNode sid (AllocaSink eclass i w)
      e = LEdge (Edge vN sid) UnconditionalEdge
  _ <- graphStateSinks %= (s:)
  _ <- graphStateEdges %= HM.insertWith (++) vN [e]
  return ()

-- | These handle fields of arguments escaping.  Before the final
-- graph construction step, edges will be added from this to
-- everything that v has an edge to.  We can't do it here because v
-- might have more edges added later.
--
-- Make a special field source - that is looked up during the escape
-- query based on its base (a).  It also needs an edge to the @v@.
fieldSource :: Value -> Argument -> AbstractAccessPath -> GraphBuilder ()
fieldSource v a p = do
  vN <- valueNode v
  nid <- nextNodeId
  let n = LNode nid (FieldSource a p)
      e = LEdge (Edge nid vN) UnconditionalEdge
  _ <- graphStateEdges %= HM.insertWith (++) nid [e]
  _ <- graphStateFieldSourceMap %= HM.insertWith (++) (toValue a) [n]
  return ()

-- | These two go together; they handle fields escaping through calls.
-- They handle fields of values escaping through calls.  The call
-- allows a field to escape (callFieldEscape) and the fieldStore tells
-- us what value was stored to that field.
--
-- @sv@ is stored into path @p@ of @base@ (by instruction @w@).
--
-- If @base@ is an argument to a function call that lets path @p@
-- escape (these are the callFieldEscape facts), then @sv@ escapes
-- (through the call).  At graph construction time, this can be
-- represented by making an edge from sv to the argument sink (which
-- can be made then).
fieldStore :: Value -> Value -> AbstractAccessPath -> Instruction -> GraphBuilder ()
fieldStore sv base p w = do
  n <- valueNode sv
  _ <- graphStateFieldStores %= HM.insertWith (++) base [(p, n, w)]
  return ()

-- | Paired with fieldStore - it implicitly creates a sink (much like
-- flowToSink) annotated with an access path
callFieldEscape :: EscapeClass -> Value -> AbstractAccessPath -> Instruction -> GraphBuilder ()
callFieldEscape eclass base p w = do
  nid <- nextNodeId
  let s = LNode nid (Sink eclass w Nothing)
  _ <- graphStateCallFieldEscapes %= HM.insertWith (++) base [(p, nid)]
  _ <- graphStateSinks %= (s:)

  -- Make a fieldSource for base since a field of base escapes.  This
  -- handles proxying an argument through a function call that lets a
  -- field escape.
  case valueContent' base of
    ArgumentC a -> do
      aid <- nextNodeId
      let an = LNode aid (FieldSource a p)
          e = LEdge (Edge aid nid) UnconditionalEdge
      _ <- graphStateEdges %= HM.insertWith (++) aid [e]
      _ <- graphStateFieldSourceMap %= HM.insertWith (++) base [an]
      return ()
    _ -> return ()

  return ()

-- FIXME at a high level, I need to add many more tests to ensure that
-- escapes by address-taken operations are handled properly.
addFact :: IndirectCallSummary
           -> DependencySummary
           -> EscapeSummary
           -> Instruction
           -> GraphBuilder ()
addFact ics ds summ inst =
  case inst of
    RetInst { retInstValue = Just rv } ->
      ifPointer rv (return ()) $ do
        flowToSink DirectEscape rv inst Nothing

    GetElementPtrInst { getElementPtrValue = base } ->
      case valueType inst of
        TypePointer (TypePointer _ _) _ -> do
          flowTo (toValue inst) base inst ForwardEdge
--          flowTo base (toValue inst) inst BackwardEdge
          case valueContent' base of
            ArgumentC a -> do
              let Just cpath = accessPath inst
              fieldSource (toValue inst) a (abstractAccessPath cpath)
            _ -> return ()
        _ -> return ()
{-
FIXME Convert this to a special case of store GEP to loc
    GetElementPtrInst { getElementPtrValue = base } ->
      case valueType inst of
        TypePointer (TypePointer _ _) _ -> do
          assertFact flowTo [ V (toValue inst), V base, W inst ]
          assertFact flowTo [ V base, V (toValue inst), W inst ]
        _ -> return ()
      -- case (accessPath inst, valueContent' base) of
      --   (Just cpath, ArgumentC a) ->
      --     -- FIXME: need to add some extra rules to match the flow
      --     -- here if the argument to the GEP isn't an argument, but is
      --     -- something that flows from an argument.
      --     assertFact fieldSource [ V (toValue inst), FieldSource a (abstractAccessPath cpath) ]
      --   _ -> return ()
-}

    -- FIXME: address of an argument escaping

    -- FIXME: probably doesn't handle something like
    --
    -- > foo(a->b)
    --
    -- where foo lets a field escape from its argument.  The correct
    -- behavior there should be to either merge the two when checking
    -- arguments or just saying that a field escaping through a field
    -- escape is a full escape (conservative)

    -- For each load, if it is loading a field of an argument, add
    -- that fact.  FIXME: We also probably need to know when the
    -- address of a field is taken (i.e., a GEP).
    LoadInst { } ->
      case accessPath inst of
        Nothing -> return ()
        Just cpath ->
          case valueContent' (accessPathBaseValue cpath) of
            ArgumentC a -> do
              fieldSource (toValue inst) a (abstractAccessPath cpath)
            _ -> return ()
    StoreInst { storeValue = sv, storeAddress = sa } ->
      ifPointer sv (return ()) $ do
        -- If the access path base is something that escapes, we make a
        -- sink for it.  Otherwise we have to make an internal node.
        --
        -- We then add an edge from sv to whatever node got added.
        let cpath = accessPath inst
            base = fmap accessPathBaseValue cpath
            absPath = fmap abstractAccessPath cpath
        -- FIXME: if the *base* of the access path is used in a call
        -- where the field described by this path escapes, we need to
        -- generate a sink here.  It is easier to do it here than in
        -- the normal call argument handler.  An alternative would be
        -- to add a new fact stating that there was a store of @sv@ to
        -- a field of @base@ (annotated with the abstract access
        -- path).  The reachability rule could then be augmented to
        -- make the connection.  Then at the call site, the argument
        -- can be marked with a special FieldEscapeSink that has the
        -- same access path.
        --
        -- FIXME: Does proxying an argument with a field escape work?
        case isSink base of
          -- If the destination isn't a sink, it is just an internal
          -- node causing some information flow.
          Nothing -> do
            flowTo sv sa inst ForwardEdge
            case (base, absPath) of
              (Just b, Just absPath') ->
                fieldStore sv b absPath' inst
              _ -> return ()
                   -- At call sites where a field escapes, assert the fact:
                   --
                   -- > assertFact fieldEscapeSink [ V base, P absPath, W inst ]
                   --
                   -- and then match them up on base/path in a secondary
                   -- escape rule (sv escapes via inst),
          Just baseVal ->
            case valueContent' baseVal of
              ArgumentC a ->
                let f = argumentFunction a
                    Just (ix, _) = find ((==a) . snd) (zip [0..] (functionParameters f))
                in flowToSink (ArgumentEscape ix) sv inst $ Just $ ArgumentDescriptor f ix
              _ -> flowToSink DirectEscape sv inst Nothing
    CallInst { callFunction = f, callArguments = args } ->
      addCallArgumentFacts ics ds summ inst f (map fst args)
    InvokeInst { invokeFunction = f, invokeArguments = args } ->
      addCallArgumentFacts ics ds summ inst f (map fst args)
    PhiNode { phiIncomingValues = ivs } ->
      ifPointer inst (return ()) $
        mapM_ (\v -> flowTo v (toValue inst) inst UnconditionalEdge) (map fst ivs)
    SelectInst { selectTrueValue = tv, selectFalseValue = fv } ->
      ifPointer inst (return ()) $ do
        flowTo tv (toValue inst) inst ForwardEdge
        flowTo fv (toValue inst) inst ForwardEdge
    BitcastInst { castedValue = cv } ->
      flowTo cv (toValue inst) inst ForwardEdge
    _ -> return ()

-- FIXME check to see if a store to a bitcast of (e.g., a global)
-- properly escapes...  hopefully we don't need bidirectional edges on
-- those and phi nodes
--
-- This would require edge labels and only edges with certain labels
-- could be followed from some kinds of nodes - this is doable with
-- xdfsWithM at least.  This would also work with GEP instructions.
--
-- The rule would be something like "Store edges can only be followed
-- after the traversal hits a store instruction on its current path".
-- Tracking paths within xdfsWithM would be difficult.  Maybe it is
-- doable by having the "neighbors" extractor tag its "store
-- successors" specially.  If the current node is store tagged, all of
-- its successors are store tagged.

addCallArgumentFacts :: IndirectCallSummary
                        -> DependencySummary
                        -> EscapeSummary
                        -> Instruction
                        -> Value
                        -> [Value]
                        -> GraphBuilder ()
addCallArgumentFacts ics ds summ ci callee args =
  case valueContent' callee of
    FunctionC f -> do
      let formals = functionParameters f
      mapM_ checkFuncArg (zip formals args)
    ExternalFunctionC f -> mapM_ (checkExt f) (zip [0..] args)
    _ ->
      case consistentTargetEscapes summ ds ics callee (length args) of
        Nothing -> mapM_ (doAssert IndirectEscape) args
        Just (Left representative) -> do
          let formals = functionParameters representative
          mapM_ checkContractFuncArg (zip formals args)
        Just (Right representative) -> do
          mapM_ (checkExtContractFuncArg representative) (zip [0..] args)
  where
    doAssert etype v =
      ifPointer v (return ()) $ flowToSink etype v ci Nothing
    argFieldAssert etype v absPath = do
      callFieldEscape etype v absPath ci
      case valueContent' v of
        ArgumentC a -> fieldSource v a absPath
        _ -> return ()
    checkExt ef (ix, arg) =
      case lookupArgumentSummary ds summ ef ix of
        Nothing -> doAssert IndirectEscape arg
        Just annots ->
          choose [ (PAEscape, doAssert DirectEscape arg)
                 , (PAFptrEscape, doAssert IndirectEscape arg)
                 , (PAContractEscape, doAssert BrokenContractEscape arg)
                 ] (return ()) annots
    checkFuncArg (formal, arg) =
      ifPointer arg (return ()) $ do
        case HM.lookup formal (summ ^. escapeArguments) of
          Just (DirectEscape, _) -> doAssert DirectEscape arg
          _ -> case HM.lookup formal (summ ^. escapeFields) of
            Just apsAndWitnesses ->
              let aps = S.toList $ S.map (\(_, fld, _) -> fld) apsAndWitnesses
                  -- FIXME we can probably also handle indirect
                  -- escapes here now, too
              in mapM_ (argFieldAssert DirectEscape arg) aps
            Nothing -> case HM.lookup formal (summ ^. escapeArguments) of
              Just (IndirectEscape, _) -> doAssert IndirectEscape arg
              -- Now if it doesn't escape legitimately, we can check
              -- the case of an escape into a local.  So there are two
              -- cases: escape into local (alloca) or proxied escape
              -- into an argument.  If it is something else,
              -- up-convert to a normal escape.
              _ ->
                case HM.lookup formal (summ ^. escapeIntoArguments) of
                  Nothing -> return ()
                  Just (eclass, func, idx) ->
                    case length args > idx of
                      False -> doAssert DirectEscape arg
                      True ->
                        case valueContent' (args !! idx) of
                          -- arg escapes (via this function call) into
                          -- a (so this is an escape by proxy).  We can
                          -- bubble this annotation up to the caller
                          ArgumentC a ->
                            let desc = ArgumentDescriptor (argumentFunction a) idx
                            in ifPointer a (return ()) $
                                 flowToSink (ArgumentEscape idx) arg ci (Just desc)
                          -- Use a SinkUnless (unless arg does not
                          -- escape).  Use a helper to check if only
                          -- this special sink is reachable.  If it is
                          -- not, filter the special sink out and
                          -- return the remaining sinks.
                          InstructionC i@AllocaInst {} ->
                            flowToAlloca eclass arg i ci
                          -- If it isn't one of those things, it just
                          -- escapes.
                          _ -> doAssert DirectEscape arg
    checkContractFuncArg (formal, arg) =
      ifPointer arg (return ()) $ do
        case HM.lookup formal (summ ^. escapeArguments) of
          Nothing -> doAssert BrokenContractEscape arg
          Just (etype, _) -> doAssert etype arg
    checkExtContractFuncArg ef (ix, arg) =
      case lookupArgumentSummary ds summ ef ix of
        -- No external summary, indirect escape
        Nothing -> doAssert IndirectEscape arg
        Just annots ->
          choose [ (PAEscape, doAssert DirectEscape arg)
                 , (PAFptrEscape, doAssert IndirectEscape arg)
                 ] (doAssert BrokenContractEscape arg) annots

-- | Execute the first matching action:
--
-- > chooseM_ actions dflt vals
--
-- The list of actions maps a value to an action.  This function takes
-- the first value that matches anything in the list of @vals@ and
-- executes it.  If none match, the default action is executed.
choose :: (Eq a) => [(a, b)] -> b -> [a] -> b
choose [] dflt _ = dflt
choose ((v,a):actions) dflt vals =
  case v `elem` vals of
    True -> a
    False -> choose actions dflt vals

-- | If all of the resolvable targets of the given call/invoke
-- instruction have the same escape properties for each argument,
-- return an arbitrary one as a representative for the analysis.
consistentTargetEscapes :: EscapeSummary
                           -> DependencySummary
                           -> IndirectCallSummary
                           -> Value
                           -> Int
                           -> Maybe (Either Function ExternalFunction)
consistentTargetEscapes summ ds ics callee argCount = do
  fs <- nonEmpty targets'
  checkConsistency summ ds fs argCount
  where
    toEither v =
      case valueContent' v of
        FunctionC f -> Just $ Left f
        ExternalFunctionC ef -> Just $ Right ef
        _ -> Nothing
    targets' = mapMaybe toEither targets
    targets = indirectCallInitializers ics callee

-- | Given a list of indirect function call targets (@fs@), return a
-- single (arbitrary) representative if all of the targets have the
-- same annotations on each argument.
checkConsistency :: EscapeSummary
                    -> DependencySummary
                    -> NonEmpty (Either Function ExternalFunction)
                    -> Int
                    -> Maybe (Either Function ExternalFunction)
checkConsistency summ ds fs argCount =
  case all isGroupConsistent annotsByPosition of
    False -> Nothing
    True -> Just (NEL.head fs)
  where
    annotsByPosition = transpose argAnnotLists
    argAnnotLists = map calleeToAnnotations (NEL.toList fs)
    -- Convert a callee to a list where each element is the (Maybe EscapeClass)
    -- inferred for that argument position
    calleeToAnnotations = either funcToAnnots extFuncToAnnots
    funcToAnnots = map (argEscapeType summ) . functionParameters
    extFuncToAnnots ef = map (extArgEscapeType summ ds ef) [0..(argCount-1)]

-- | Check if the escape annotations for each argument are consistent
-- across all known call targets.  Nothing indicates that there is no
-- escape.
isGroupConsistent :: [Maybe EscapeClass] -> Bool
isGroupConsistent [] = True
isGroupConsistent (ec:ecs) =
  all (== ec) ecs

extArgEscapeType :: EscapeSummary -> DependencySummary -> ExternalFunction -> Int -> Maybe EscapeClass
extArgEscapeType summ ds ef ix = do
  annots <- lookupArgumentSummary ds summ ef ix
  choose [ (PAEscape, return DirectEscape)
         , (PAFptrEscape, return IndirectEscape)
         , (PAContractEscape, return BrokenContractEscape)
         ] Nothing annots

-- This stuff doesn't deal with field escapes yet...
argEscapeType :: EscapeSummary -> Argument -> Maybe EscapeClass
argEscapeType summ a = do
  (e, _) <- HM.lookup a (summ ^. escapeArguments)
  return e

-- Testing

-- | Extract the arguments for each function that escape.  The keys of
-- the map are function names and the set elements are argument names.
-- This format exposes the internal results for testing purposes.
--
-- For actual use in a program, use one of 'functionEscapeArguments',
-- 'functionWillEscapeArguments', or 'instructionEscapes' instead.
escapeResultToTestFormat :: EscapeSummary -> Map String (Set (EscapeClass, String))
escapeResultToTestFormat er =
  M.filter (not . S.null) $ foldr fieldTransform argEscapes (HM.toList fm)
  where
    directEscapes = foldr transform mempty (HM.toList m)
    argEscapes = foldr argTransform directEscapes (HM.toList am)
    m = er ^. escapeArguments
    fm = er ^. escapeFields
    am = er ^. escapeIntoArguments
    argTransform (a, (tag, _, _)) acc =
      let aname = show (argumentName a)
          f = argumentFunction a
          fname = show (functionName f)
      in M.insertWith' S.union fname (S.singleton (tag, aname)) acc
    transform (a, (tag, _)) acc =
      let f = argumentFunction a
          fname = show (functionName f)
          aname = show (argumentName a)
      in M.insertWith' S.union fname (S.singleton (tag, aname)) acc
    fieldTransform (a, fieldsAndInsts) acc =
      let f = argumentFunction a
          fname = show (functionName f)
          aname = show (argumentName a)
          tagsAndFields = S.toList $ S.map (\(tag, fld, _) -> (tag, fld)) fieldsAndInsts
          newEntries = S.fromList $ mapMaybe (toFieldRef aname) tagsAndFields
      in M.insertWith' S.union fname newEntries acc
    toFieldRef aname (tag, fld) =
      case abstractAccessPathComponents fld of
        [AccessDeref, AccessField ix] -> Just $ (tag, printf "%s.<%d>" aname ix)
        _ -> Nothing

escapeUseGraphs :: EscapeSummary -> [(String, ValueFlowGraph)]
escapeUseGraphs = map (second (^. escapeVFG)) . map (first (show . functionName)) . HM.toList . (^. escapeGraph)

useGraphvizParams :: GraphvizParams n ValueFlowNode el () ValueFlowNode
useGraphvizParams =
  nonClusteredParams { fmtNode = \(_, l) -> [toLabel l]
                     , fmtEdge = \_ -> []
                     }

useGraphvizRepr :: ValueFlowGraph -> DotGraph Int
useGraphvizRepr g = graphElemsToDot useGraphvizParams ns es
  where
    ns = map toNodeTuple $ labNodes g
    es = map toEdgeTuple $ labEdges g
