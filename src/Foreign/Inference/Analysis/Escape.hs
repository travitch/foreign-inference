{-# LANGUAGE TemplateHaskell, OverloadedStrings, FlexibleContexts #-}
module Foreign.Inference.Analysis.Escape (
  EscapeSummary,
  identifyEscapes,
  instructionEscapes,
  instructionEscapesWith,

  -- * Testing
  EscapeClass(..),
  escapeResultToTestFormat,
  ) where

import Control.DeepSeq
import Control.Monad.State.Strict
import Control.Monad.Writer ( runWriter )
import Data.Default
import Data.Lens.Strict
import Data.Hashable
import Data.HashMap.Strict ( HashMap )
import qualified Data.HashMap.Strict as HM
import Data.List ( transpose )
import Data.List.NonEmpty ( NonEmpty, nonEmpty )
import qualified Data.List.NonEmpty as NEL
import Data.Map ( Map )
import qualified Data.Map as M
import Data.Maybe ( fromMaybe, mapMaybe )
import Data.Set ( Set )
import qualified Data.Set as S
import Data.Lens.Template
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

-- import Text.Printf
-- import Debug.Trace
-- debug = flip trace

-- | The ways a value can escape from a function
data EscapeClass = DirectEscape
                 | BrokenContractEscape
                 | IndirectEscape
                 deriving (Eq, Ord, Read, Show)

instance Hashable EscapeClass where
  hash DirectEscape = 76
  hash BrokenContractEscape = 699
  hash IndirectEscape = 5

instance NFData EscapeClass

data ValueFlowNode = Sink { sinkClass :: EscapeClass
                          , sinkWitness :: Instruction
                          , sinkPath :: Maybe AbstractAccessPath
                          }
                   | Location { locationValue :: Value }
                   | FieldSource { fieldSourceArgument :: Argument
                                 , fieldSourcePath :: AbstractAccessPath
                                 }
                   deriving (Eq, Ord, Show)

instance NFData ValueFlowNode where
  rnf (Sink c w p) = c `deepseq` w `deepseq` p `deepseq` ()
  rnf (Location v) = v `deepseq` ()
  rnf (FieldSource a p) = a `deepseq` p `deepseq` ()

type ValueFlowGraph = Gr ValueFlowNode ()

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

$(makeLens ''GraphState)

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
  } deriving (Eq)

instance NFData EscapeGraph where
  rnf (EscapeGraph m fm g) = g `deepseq` m `deepseq` fm `deepseq` ()

$(makeLens ''EscapeGraph)

-- | The monad in which we construct the value flow graph
type GraphBuilder = State GraphState

data EscapeSummary =
  EscapeSummary { _escapeGraph :: HashMap Function EscapeGraph
                , _escapeArguments :: HashMap Argument (EscapeClass, Instruction)
                , _escapeFields :: HashMap Argument (Set (EscapeClass, AbstractAccessPath, Instruction))
                , _escapeDiagnostics :: Diagnostics
                }

$(makeLens ''EscapeSummary)

instance Show EscapeSummary where
  show (EscapeSummary _ ea ef _) = show ea ++ "/" ++ show ef

instance Eq EscapeSummary where
  (EscapeSummary g1 ea1 ef1 _) == (EscapeSummary g2 ea2 ef2 _) =
    g1 == g2 && ea1 == ea2 && ef1 == ef2

instance Default EscapeSummary where
  def = EscapeSummary mempty mempty mempty mempty

instance Monoid EscapeSummary where
  mempty = def
  mappend (EscapeSummary g1 as1 was1 d1) (EscapeSummary g2 as2 was2 d2) =
    EscapeSummary { _escapeGraph = HM.union g1 g2
                  , _escapeArguments = HM.union as1 as2
                  , _escapeFields = HM.union was1 was2
                  , _escapeDiagnostics = d1 `mappend` d2
                  }

instance NFData EscapeSummary where
  rnf r@(EscapeSummary g as was d) =
    g `deepseq` as `deepseq` was `deepseq` d `deepseq` r `seq` ()

instance HasDiagnostics EscapeSummary where
  diagnosticLens = escapeDiagnostics

instance SummarizeModule EscapeSummary where
  summarizeFunction _ _ = []
  summarizeArgument = summarizeEscapeArgument

-- FIXME: Here is an easy improvement - note when values escape into
-- an argument (and which one).  This will let us use this information
-- in a caller and, if the argument being escaped into from a callee
-- is just a local non-escaping value, we can ignore it since it isn't
-- a real escape.  This prevents us from having to unify the caller
-- context with all callee contexts.

-- | This is the underlying bottom-up analysis to identify which
-- arguments escape.  It builds an EscapeGraph for the function
-- (incorporating information from other functions that have already
-- been analyzed) and then checks to see which arguments escape using
-- that graph.
identifyEscapes :: (FuncLike funcLike, HasFunction funcLike)
                   => DependencySummary
                   -> IndirectCallSummary
                   -> Lens compositeSummary EscapeSummary
                   -> ComposableAnalysis compositeSummary funcLike
identifyEscapes ds ics lns =
  composableAnalysisM runner escapeWrapper lns
  where
    escapeWrapper funcLike s = do
      let f = getFunction funcLike
          g = buildValueFlowGraph ics extSumm s (functionInstructions f)
          s' = foldr (summarizeArgumentEscapes g) s (functionParameters f)
      return $ (escapeGraph ^!%= HM.insert f g) s'

    runner a =
      let (e, diags) = runWriter a
      in (escapeDiagnostics ^= diags) e

    extSumm ef ix =
      -- FIXME: Switch the builder to be a StateT so we can let this
      -- monadic extsumm record missing summaries
      case lookupArgumentSummary ds (undefined :: EscapeSummary) ef ix of
        Nothing -> True --  do
          -- let msg = "Missing summary for " ++ show (externalFunctionName ef)
          -- emitWarning Nothing "EscapeAnalysis" msg
          -- return True
        Just annots -> PAEscape `elem` annots

-- | A generalization of 'instructionEscapes'.  The first argument is
-- a predicate that returns True if the input Instruction (which is a
-- sink) should be excluded in the Escape graph.  The set of reachable
-- locations for the input instruction is computed as normal, but the
-- instructions in the @ignore@ list are removed from the set before
-- it is used to determine what escapes.
--
-- This arrangement means that @ignore@d nodes do *not* affect the
-- reachability computation.  That is critical for transitive
-- assignments to be treated properly (that is, for the transitive
-- links to be included).
--
-- The intended use of this variant is to issue escape queries for
-- instructions that are known to escape via some desired means (e.g.,
-- an out parameter) and to determine if they also escape via some
-- other means.  In that case, the @ignore@ list should be just the
-- store instruction that created the known escape.
instructionEscapesWith :: (Instruction -> Bool) -> Instruction -> EscapeSummary -> Maybe Instruction
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
instructionEscapeCore ignorePred i (EscapeSummary eg _ _ _) = do
  ln <- HM.lookup (toValue i) m
  case reachableSinks (unlabelNode ln) g ignorePred of
    [] -> Nothing
    (Sink _ w _) : _ -> return w
    _ -> error "Non-sink in reachableSinks result"
  where
    Just bb = instructionBasicBlock i
    f = basicBlockFunction bb
    errMsg = error ("Missing summary for function " ++ show (functionName f))
    EscapeGraph m _ g = HM.lookupDefault errMsg f eg

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



summarizeArgumentEscapes :: EscapeGraph -> Argument -> EscapeSummary -> EscapeSummary
summarizeArgumentEscapes eg a s =
  case entireArgumentEscapes eg a s of
    (True, s') -> s'
    (False, _) -> argumentFieldsEscape eg a s

-- | This is basically DFS.  Note that we need to generalize this for
-- the instructionEscapes* functions.
--
-- Also note that for any reachable store, a follow up query must be
-- issued to see if any sinks are reachable following store edges
-- (once that functionality is implemented).  Be sure to remember
-- stores that have been processed so that it doesn't loop forever.
-- The recursive traversals should occur here so that clients only
-- need to look for sinks.
--
-- Handle ignored instructions in the neighbor computation.  If a
-- neighbor is a sink, and its witness is being ignored, do not
-- include it in the neighbor set.
reachableSinks :: Int -> ValueFlowGraph -> (Instruction -> Bool) -> [ValueFlowNode]
reachableSinks nodeId g ignoredPred =
  filter isSinkNode (doReach g)
  where
    isSinkNode (Sink _ _ _) = True
    isSinkNode _ = False
    doReach = xdfsWith contextNeighbors contextToReached [nodeId]
    contextNeighbors c =
      filter sinkWitnessNotIgnored (neighbors' c)
    sinkWitnessNotIgnored nid =
      case lab g nid of
        Nothing -> error "Missing label in reachableSinks"
        Just (Sink _ w _) -> not (ignoredPred w)
        _ -> True

contextToReached :: Context ValueFlowGraph -> ValueFlowNode
contextToReached (Context _ (LNode _ l) _) = l

entireArgumentEscapes :: EscapeGraph -> Argument -> EscapeSummary -> (Bool, EscapeSummary)
entireArgumentEscapes eg a s =
  case HM.lookup (toValue a) (eg ^. escapeGraphValueMap) of
    Nothing -> (False, s)
    Just (LNode nid _) ->
      case reachableSinks nid (eg ^. escapeVFG) (const False) of
        -- No non-field escapes, signal the caller to try to find
        -- field escapes instead
        [] -> (False, s)
        -- Otherwise, take the first sink
        (Sink eclass w _) : _ ->
          let s' = (escapeArguments ^!%= HM.insert a (eclass, w)) s
          in (True, s')
        _ -> error "Non-sink found in reachableSinks result"

argumentFieldsEscape :: EscapeGraph -> Argument -> EscapeSummary -> EscapeSummary
argumentFieldsEscape eg a s =
  case HM.lookup (toValue a) (eg ^. escapeGraphFieldSourceMap) of
    -- No fields escape either
    Nothing -> s
    Just fieldSrcs -> foldr checkFieldEscapes s fieldSrcs
  where
    checkFieldEscapes (LNode fldSrcId (FieldSource arg p)) summ =
      case reachableSinks fldSrcId (eg ^. escapeVFG) (const False) of
        [] -> summ
        (Sink eclass w _) : _ ->
          let newEsc = S.singleton (eclass, p, w)
          in (escapeFields ^!%= HM.insertWith S.union arg newEsc) summ
        _ -> error "Non-sink found in reachableSinks result"

isSink :: Maybe Value -> Bool
isSink v =
  case v of
    Nothing -> False
    Just vv ->
      case valueContent' vv of
        ArgumentC _ -> True
        GlobalVariableC _ -> True
        ExternalValueC _ -> True
        InstructionC (CallInst {}) -> True
        InstructionC (InvokeInst {}) -> True
        _ -> False

-- | A helper to abstract the pointer type tests.  If the value @v@ is
-- not a pointer, return @defVal@.  Otherwise, return @isPtrVal@.
-- This helps remove a level of nested (and repetitive) pattern
-- matching.
ifPointer :: IsValue v => v -> a -> a -> a
ifPointer v defVal isPtrVal =
  case valueType v of
    TypePointer _ _ -> isPtrVal
    _ -> defVal

buildValueFlowGraph :: IndirectCallSummary
                       -> (ExternalFunction -> Int -> Bool)
                       -> EscapeSummary
                       -> [Instruction]
                       -> EscapeGraph
buildValueFlowGraph ics extSumm summ is =
  EscapeGraph { _escapeGraphValueMap = sN ^. graphStateValueMap
              , _escapeGraphFieldSourceMap = sN ^. graphStateFieldSourceMap
              , _escapeVFG = mkGraph ns es -- `debug` printf "Nodes:\n%s\nEdges:\n%s\n" (show ns) (show es)
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
    b = mapM_ (addFact ics extSumm summ) is
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
    makeEdge p1 dest (p2, src, _) =
      case p1 == p2 of
        False -> Nothing
        True -> Just $ LEdge (Edge src dest) ()

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
  nid <- access graphStateIdSrc
  _ <- graphStateIdSrc !%= (+1)
  return nid

-- | Create a node for the given value if it does not already exist.
-- Returns the corresponding unique node id.
valueNode :: Value -> GraphBuilder Int
valueNode v = do
  vm <- access graphStateValueMap
  case HM.lookup v vm of
    Just n -> return (unlabelNode n)
    Nothing -> do
      nid <- nextNodeId
      let n = LNode nid (Location v)
      _ <- graphStateValueMap !%= HM.insert v n
      return nid

-- | Values flow from v1 to v2
flowTo :: Value -> Value -> Instruction -> GraphBuilder ()
flowTo from to w = do
  fromN <- valueNode from
  toN <- valueNode to
  let e = LEdge (Edge fromN toN) ()
  _ <- graphStateEdges !%= HM.insertWith (++) fromN [e]
  return ()

-- | The value named flows to a sink.  This should create a new node
-- (each sink is accompanied by a flowTo).  Having it make a new node
-- allows us to have each argument be a sink without requiring fancy
-- handling of arguments (seeing if they are in a loop, &c)
flowToSink :: EscapeClass -> Value -> Instruction -> GraphBuilder ()
flowToSink eclass v w = do
  -- The value node
  vN <- valueNode v
  -- A virtual node representing the sink
  sid <- nextNodeId
  let s = LNode sid (Sink eclass w Nothing)
      e = LEdge (Edge vN sid) ()
  _ <- graphStateEdges !%= HM.insertWith (++) vN [e]
  _ <- graphStateSinks !%= (s:)
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
      e = LEdge (Edge nid vN) ()
  _ <- graphStateEdges !%= HM.insertWith (++) nid [e]
  _ <- graphStateFieldSourceMap !%= HM.insertWith (++) (toValue a) [n]
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
  _ <- graphStateFieldStores !%= HM.insertWith (++) base [(p, n, w)]
  return ()

-- | Paired with fieldStore - it implicitly creates a sink (much like
-- flowToSink) annotated with an access path
callFieldEscape :: EscapeClass -> Value -> AbstractAccessPath -> Instruction -> GraphBuilder ()
callFieldEscape eclass base p w = do
  nid <- nextNodeId
  let s = LNode nid (Sink eclass w (Just p))
  _ <- graphStateCallFieldEscapes !%= HM.insertWith (++) base [(p, nid)]
  _ <- graphStateSinks !%= (s:)

  -- Make a fieldSource for base since a field of base escapes.  This
  -- handles proxying an argument through a function call that lets a
  -- field escape.
  case valueContent' base of
    ArgumentC a -> do
      aid <- nextNodeId
      let an = LNode aid (FieldSource a p)
          e = LEdge (Edge aid nid) ()
      _ <- graphStateEdges !%= HM.insertWith (++) aid [e]
      _ <- graphStateFieldSourceMap !%= HM.insertWith (++) base [an]
      return ()
    _ -> return ()

  return ()

-- FIXME at a high level, I need to add many more tests to ensure that
-- escapes by address-taken operations are handled properly.
addFact :: IndirectCallSummary
           -> (ExternalFunction -> Int -> Bool)
           -> EscapeSummary
           -> Instruction
           -> GraphBuilder ()
addFact ics extSumm summ inst =
  case inst of
    RetInst { retInstValue = Just rv } ->
      ifPointer rv (return ()) $ do
        flowToSink DirectEscape rv inst
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
    StoreInst { storeValue = sv, storeAddress = sa } -> do
      -- If the access path base is something that escapes, we make a
      -- sink for it.  Otherwise we have to make an internal node.
      --
      -- We then add an edge from sv to whatever node got added.
      let cpath = accessPath inst
          base = fmap accessPathBaseValue cpath
          absPath = fmap abstractAccessPath cpath
      -- FIXME: if the *base* of the access path is used in a call
      -- where the field described by this path escapes, we need to
      -- generate a sink here.  It is easier to do it here than in the
      -- normal call argument handler.  An alternative would be to add
      -- a new fact stating that there was a store of @sv@ to a field
      -- of @base@ (annotated with the abstract access path).  The
      -- reachability rule could then be augmented to make the
      -- connection.  Then at the call site, the argument can be
      -- marked with a special FieldEscapeSink that has the same
      -- access path.
      --
      -- FIXME: Does proxying an argument with a field escape work?
      case isSink base of
        -- If the destination isn't a sink, it is just an internal
        -- node causing some information flow.
        False -> do
          flowTo sv sa inst
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
        True -> flowToSink DirectEscape sv inst
    CallInst { callFunction = f, callArguments = args } ->
      addCallArgumentFacts ics extSumm summ inst f (map fst args)
    InvokeInst { invokeFunction = f, invokeArguments = args } ->
      addCallArgumentFacts ics extSumm summ inst f (map fst args)
    PhiNode { phiIncomingValues = ivs } ->
      mapM_ (\v -> flowTo v (toValue inst) inst) (map fst ivs)
    SelectInst { selectTrueValue = tv, selectFalseValue = fv } -> do
      flowTo tv (toValue inst) inst
      flowTo fv (toValue inst) inst
    BitcastInst { castedValue = cv } ->
      flowTo cv (toValue inst) inst
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
                        -> (ExternalFunction -> Int -> Bool)
                        -> EscapeSummary
                        -> Instruction
                        -> Value
                        -> [Value]
                        -> GraphBuilder ()
addCallArgumentFacts ics extSumm summ ci callee args =
  case valueContent' callee of
    FunctionC f -> do
      let formals = functionParameters f
      mapM_ checkFuncArg (zip formals args)
    ExternalFunctionC f -> mapM_ (checkExt f) (zip [0..] args)
    _ ->
      case consistentTargetEscapes summ ics ci of
        Nothing -> mapM_ (doAssert IndirectEscape) args
        Just representative -> do
          let formals = functionParameters representative
          mapM_ checkContractFuncArg (zip formals args)
  where
    doAssert etype v = flowToSink etype v ci
    argFieldAssert etype v absPath = do
      callFieldEscape etype v absPath ci
      case valueContent' v of
        ArgumentC a -> fieldSource v a absPath
        _ -> return ()
    checkExt ef (ix, arg) =
      case extSumm ef ix of
        False -> return ()
        True -> doAssert DirectEscape arg
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
              _ -> return ()
    checkContractFuncArg (formal, arg) =
      ifPointer arg (return ()) $ do
        case HM.lookup formal (summ ^. escapeArguments) of
          Nothing -> doAssert BrokenContractEscape arg
          Just (etype, _) -> doAssert etype arg


-- | If all of the resolvable targets of the given call/invoke
-- instruction have the same escape properties for each argument,
-- return an arbitrary one as a representative for the analysis.
consistentTargetEscapes :: EscapeSummary -> IndirectCallSummary -> Instruction -> Maybe Function
consistentTargetEscapes summ ics ci = do
  fs <- nonEmpty targets
  checkConsistency summ fs
  where
    targets = indirectCallTargets ics ci

checkConsistency :: EscapeSummary -> NonEmpty Function -> Maybe Function
checkConsistency summ fs =
  case all (groupConsistent summ) formalsByPosition of
    False -> Nothing
    True -> Just (NEL.head fs)
  where
    formalLists = map functionParameters (NEL.toList fs)
    formalsByPosition = transpose formalLists

groupConsistent :: EscapeSummary -> [Argument] -> Bool
groupConsistent _ [] = True
groupConsistent summ (a:as) =
  all (== (argEscapeType summ a)) (map (argEscapeType summ) as)

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
  M.filter (not . S.null) $ foldr fieldTransform directEscapes (HM.toList fm)
  where
    directEscapes = foldr transform mempty (HM.toList m)
    m = er ^. escapeArguments
    fm = er ^. escapeFields
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
