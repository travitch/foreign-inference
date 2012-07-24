{-# LANGUAGE TemplateHaskell, ViewPatterns, FlexibleInstances, TypeSynonymInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- | This is a very conservative flow- and context-insensitive (but
-- field-sensitive) escape analysis based on graph reachability.  The
-- underlying graph is an escape graph where escapes are represented by
-- sinks and arguments are sources.  For nodes A and B, there is an edge
-- from A to B if the pointer A is stored into B.  A value escapes if any
-- sink is reachable from it.
--
-- The notion of escape is very specific.  A pointer escapes if,
-- directly or indirectly:
--
--  * It is stored into an argument or a field of an argument
--
--  * It is stored into a global or a field of a global
--
--  * It is returned from a function
--
--  * It is passed as an argument to a function (and escapes in the callee).
--
-- There is a special case for the last point.  If a pointer is passed
-- as an argument to a call through a function pointer, it techincally
-- escapes.  Often, this is unnecessarily strict, so escapes through
-- function pointers are classified separately so that they can be
-- ignored if desired.  Escapes through function pointers are
-- superceded by true escapes.
--
-- Each argument to a function is represented by an ArgumentSource
-- node.  A load of an argument field is a FieldSource.  Stores to
-- globals and arguments are sinks.  Stores to fields of globals and
-- arguments are also sinks.  Returns are sinks.
--
-- Loads create nodes, stores add edges.
--
-- Notes on precision:
--
-- This analysis does not do any sophisticated value tracking through
-- memory references and it does not distinguish stores to locals
-- (allocas) from stores to globals.  With no optimization, it will
-- provide useless results (basically everything will escape).
--
-- With simple optimizations (-mem2reg and -basicaa) it will be very
-- precise.
--
--
-- Algorithm:
--
-- 1) Collect a @Map Instruction [AccessPath]@ that describes the fields
-- of each alloca instruction passed to them that escapes.  Entries in
-- this map are made for each call instruction argument that allows a(t
-- least one) field to escape.
--
-- > call void @fldEsc(%struct.S* %s)
--
-- If this call allows the sP field of %s to escape, the resuling Map
-- entry is:
--
-- > %s -> [Field 0]
--
-- Also collect a set of values passed to escaping function arguments.
--
-- 2) Populate the escape graph.  Arguments get ArgSrc nodes.  Loads of
-- GEPs (rooted at arguments) get FieldSource nodes.  All other
-- instructions that are pointer-typed get SimpleSrc nodes.  If the base
-- of a GEP Load is in the field escape map AND the field matches one of
-- the access paths in the map, make an edge from the src to a
-- FieldEscapeSink.
--
-- For each value in the normal escape set, make an edge from the source
-- to the appropriate escapesink node.
--
-- Stores add edges, loads add internal nodes.
--
-- 3) All ArgumentSource nodes that reach a Sink escape.  If the sink is
-- a FieldEscapeSink, they escape through a field (though the distinction
-- doesn't really matter).
--
-- Later queries will similarly only check to see if the instruction can
-- reach a sink.  There will need to be a bit of filtering done on sinks
-- in the same way as now, but the filtering now has to unwrap the node
-- type instead of being able to just look directly at the node Value.
-- If the only reachable sink is a FptrSink, treat this as we do in the
-- case where the Value is tupled with True now.
module Foreign.Inference.Analysis.Escape (
  EscapeSummary,
  identifyEscapes,
  instructionEscapes,
  instructionEscapesWith,

  -- * Testing
  EscapeGraph,
  EscapeClass(..),
  escapeResultToTestFormat,
  escapeUseGraphs,
  useGraphvizRepr
  ) where

import Control.Arrow
import Control.DeepSeq
import Control.Monad.Writer
import Data.Default
import Data.Function ( on )
import Data.GraphViz
import Data.Lens.Common
import Data.Lens.Template
import Data.List ( find, foldl', groupBy, maximumBy, sortBy, transpose )
import Data.List.NonEmpty ( NonEmpty, nonEmpty )
import qualified Data.List.NonEmpty as NEL
import Data.HashMap.Strict ( HashMap )
import qualified Data.HashMap.Strict as HM
import Data.Map ( Map )
import qualified Data.Map as M
import Data.Maybe ( fromMaybe, listToMaybe, mapMaybe )
import Data.Ord ( comparing )
import Data.Set ( Set )
import qualified Data.Set as S
import Debug.Trace.LocationTH
import Text.Printf

import Data.Graph.Interface
import Data.Graph.LazyHAMT
import Data.Graph.Algorithms.Matching.DFS
import Data.Graph.Algorithms.Matching.SP

import LLVM.Analysis
import LLVM.Analysis.AccessPath
import LLVM.Analysis.CallGraphSCCTraversal

import Foreign.Inference.Diagnostics
import Foreign.Inference.Interface
import Foreign.Inference.Analysis.IndirectCallResolver

import Debug.Trace
debug = flip trace

-- | The acctual graph type
type EscapeGraph = Gr NodeType ()
type EscapeNode = LNode EscapeGraph
type EscapeEdge = LEdge EscapeGraph
type EscapeContext = Context EscapeGraph

instance Eq EscapeGraph where
  (==) = graphEqual

data NodeType = ArgumentSource Argument
              | FieldSource { fieldSourceArgument :: Argument
                            , sinkInstruction :: Instruction
                            , fieldSourcePath :: AbstractAccessPath
                            }
                -- ^ Load (GEP Argument).  The Instruction field is
                -- the load instruction that generated the node; we
                -- need this to be able to remove the node from the
                -- reached list if it isn't in a cycle while doing
                -- argument reachability
              | CallSource { sinkInstruction :: Instruction }
                -- ^ Non-void call inst
              | FptrSink { sinkInstruction :: Instruction }
                -- ^ Indirect call inst
              | ContractSink { sinkInstruction :: Instruction }
                -- ^ Indirect call with library initializers that have
                -- consistent escape properties
              | EscapeSink { sinkInstruction :: Instruction }
                -- ^ Passing a value to an escaping call argument
              | WillEscapeSink { sinkInstruction :: Instruction }
              | InternalNode { sinkInstruction :: Instruction
                             , internalNodeValue :: Value
                             }
                -- ^ Other relevant nodes that pass references around.
                -- This can't just be an Instruction because it could
                -- be an Argument (constants and globals don't
                -- actually matter for this analysis)
              deriving (Eq, Ord, Show)

-- | The ways a value can escape from a function
data EscapeClass = DirectEscape
                 | BrokenContractEscape
                 | IndirectEscape
                 deriving (Eq, Ord, Read, Show)

instance NFData EscapeClass

data EscapeSummary =
  EscapeSummary { _escapeGraphs :: HashMap Function EscapeGraph
                , _escapeArguments :: HashMap Argument (EscapeClass, Instruction)
                , _escapeFields :: HashMap Argument (Set (EscapeClass, AbstractAccessPath, Instruction))
                , _escapeDiagnostics :: Diagnostics
                }

$(makeLens ''EscapeSummary)

instance Show EscapeSummary where
  show (EscapeSummary _ ea _ _) = show ea

instance Eq EscapeSummary where
  (EscapeSummary eg1 ea1 ef1 _) == (EscapeSummary eg2 ea2 ef2 _) =
    eg1 == eg2 && ea1 == ea2 && ef1 == ef2

instance Default EscapeSummary where
  def = EscapeSummary mempty mempty mempty mempty

instance Monoid EscapeSummary where
  mempty = def
  mappend (EscapeSummary gs1 as1 was1 d1) (EscapeSummary gs2 as2 was2 d2) =
    EscapeSummary { _escapeGraphs = HM.union gs1 gs2
                  , _escapeArguments = HM.union as1 as2
                  , _escapeFields = HM.union was1 was2
                  , _escapeDiagnostics = d1 `mappend` d2
                  }

instance NFData EscapeSummary where
  rnf r@(EscapeSummary gs as was d) =
    gs `deepseq` as `deepseq` was `deepseq` d `deepseq` r `seq` ()

instance HasDiagnostics EscapeSummary where
  diagnosticLens = escapeDiagnostics

-- | An object to hold information about which values in a function
-- are used in call argument positions that let them escape (both
-- directly and via fields).  We also store information about the
-- arguments passed to indirect function calls.
--
-- This is built up in a preprocessing step.
--
-- FIXME: The last three members should all just be one, with a (Tag,
-- Instruction)
data CallEscapes = CallEscapes { _fieldEscapes :: HashMap Value [AbstractAccessPath]
                               , _valueEscapes :: HashMap Value (EscapeClass, Instruction)
                               }

instance Default CallEscapes where
  def = CallEscapes mempty mempty

$(makeLens ''CallEscapes)

instance NFData NodeType where
  rnf (ArgumentSource a) = a `seq` ()
  rnf (FieldSource a i aap) = a `seq` i `seq` aap `seq` ()
  rnf (CallSource i) = i `seq` ()
  rnf (FptrSink i) = i `seq` ()
  rnf (ContractSink i) = i `seq` ()
  rnf (EscapeSink i) = i `seq` ()
  rnf (WillEscapeSink i) = i `seq` ()
  rnf (InternalNode i v) = i `seq` v `seq` ()

instance Labellable NodeType where
  toLabelValue (ArgumentSource a) = toLabelValue $ "Arg " ++ show a
  toLabelValue (FieldSource a _ aap) = toLabelValue $ "FldSrc " ++ show a ++ "@" ++ show aap
  toLabelValue (CallSource i) = toLabelValue $ "CallSrc " ++ show i
  toLabelValue (FptrSink i) = toLabelValue $ "FptrSink " ++ show i
  toLabelValue (ContractSink i) = toLabelValue $ "ContractSink " ++ show i
  toLabelValue (EscapeSink i) = toLabelValue $ "EscSink " ++ show i
  toLabelValue (WillEscapeSink i) = toLabelValue $ "WillEscSink " ++ show i
  toLabelValue (InternalNode i v) =
    let s :: String
        s = printf "Int %s (from %s)" (show v) (show i)
    in toLabelValue s

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

instance SummarizeModule EscapeSummary where
  summarizeFunction _ _ = []
  summarizeArgument = summarizeEscapeArgument

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
instructionEscapeCore ignoreValue i er = do
  escNode <- find nodeIsAnySink reached
  return $! sinkInstruction (nodeLabel escNode)
  where
    Just bb = instructionBasicBlock i
    f = basicBlockFunction bb
    errMsg = $failure ("Expected escape graph for " ++ show (functionName f))
    g = HM.lookupDefault errMsg f (er ^. escapeGraphs)
    instFilter = filter ((/= valueUniqueId i) . unlabelNode)
    reached0 = reachableValues $__LOCATION__ instFilter (valueUniqueId i) g
    reached = filter notIgnoredSink reached0
    notIgnoredSink nt =
      case nodeLabel nt of
        FptrSink sink -> not (ignoreValue sink)
        EscapeSink sink -> not (ignoreValue sink)
        WillEscapeSink sink -> not (ignoreValue sink)
        _ -> True

-- | Get the list of values reachable from the given instruction in
-- the use graph.
--
-- This function takes a custom filter function to transform the list
-- of reachable nodes.  The idea is that some uses need to remove the
-- input node (or other nodes depending on the context).  This
-- encapsulates the reachability and re-labeling computations.
reachableValues :: String -> ([EscapeNode] -> [EscapeNode])
                   -> Node EscapeGraph -> EscapeGraph -> [EscapeNode]
reachableValues loc filt n g =
  filt reached
  where
    reached = map (safeLab loc g) $ dfs [n] g

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
      callEscapes <- foldM (buildEscapeMaps extSumm s ics) def (functionInstructions f)
      let g = buildEscapeGraph callEscapes f
          summ1 = (escapeGraphs ^!%= HM.insert f g) s
      return $! foldr (summarizeArgumentEscapes g) summ1 (labNodes g)

    runner a =
      let (e, diags) = runWriter a
      in (escapeDiagnostics ^= diags) e

    extSumm ef ix =
      case lookupArgumentSummary ds (undefined :: EscapeSummary) ef ix of
        Nothing -> do
          let msg = "Missing summary for " ++ show (externalFunctionName ef)
          emitWarning Nothing "EscapeAnalysis" msg
          return True
        Just annots -> return $ PAEscape `elem` annots

-- | For the given 'EscapeNode' input, if it is an argument source,
-- run a reachability computation and see if it reaches any sinks.  If
-- it does, the argument (or field) escapes.
--
-- Note that the DFS in each case should start from n - the input
-- node.  FieldSources do not have the ID of their Argument (because
-- arguments can have multiple fields, the FieldSource has the ID of
-- the relevant Load instruction).
summarizeArgumentEscapes :: EscapeGraph -> EscapeNode -> EscapeSummary -> EscapeSummary
summarizeArgumentEscapes g n summ =
  case nodeLabel n of
    -- In this case, the input node is a normal argument so we are
    -- using the normal escape lenses (escapeArguments and
    -- fptrEscapeArguments).
    ArgumentSource a -> ifPointer a summ $
      let loopFilter = removeValueIfNotInLoop a g
          reached = reachableValues $__LOCATION__ loopFilter (unlabelNode n) g
      in case sinkType reached of
        SinkNormal sink ->
          case nodeLabel sink of
            ArgumentSource _ ->
              -- The argument for this node is escaping into another argument
              let w:_ = storesInPath $__LOCATION__ n sink g
              in (escapeArguments ^!%= HM.insert a (DirectEscape, w)) summ
            FieldSource _ fsi _ ->
              -- The argument for this node is escaping into the field
              -- of an argument
              let ws = storesInPath $__LOCATION__ n sink g
                  w = fromMaybe fsi (listToMaybe ws)
              in (escapeArguments ^!%= HM.insert a (DirectEscape, w)) summ
            _ -> (escapeArguments ^!%= HM.insert a (DirectEscape, sinkInstruction (nodeLabel sink))) summ
        SinkFptr fsink ->
          let newVal = (IndirectEscape, sinkInstruction (nodeLabel fsink))
          in (escapeArguments ^!%= HM.insert a newVal) summ
        SinkContract sink ->
          let newVal = (BrokenContractEscape, sinkInstruction (nodeLabel sink))
          in (escapeArguments ^!%= HM.insert a newVal) summ
        SinkNone -> summ

    -- In this case, the field of an argument is escaping somewhere.
    -- This is what gives us field sensitivity.
    FieldSource a i absPath -> ifPointer a summ $
      let loopFilter = removeValueIfNotInLoop i g
          reached = reachableValues $__LOCATION__ loopFilter (unlabelNode n) g
      in case sinkType reached of
        SinkNormal sink ->
          case nodeLabel sink of
            ArgumentSource _ ->
              let w:_ = storesInPath $__LOCATION__ n sink g
              in (escapeFields ^!%= HM.insertWith S.union a (S.singleton (DirectEscape, absPath, w))) summ
            FieldSource _ fsi _ ->
              let ws = storesInPath $__LOCATION__ n sink g
                  w = fromMaybe fsi (listToMaybe ws)
              in (escapeFields ^!%= HM.insertWith S.union a (S.singleton (DirectEscape, absPath, w))) summ
            _ -> (escapeFields ^!%= HM.insertWith S.union a (S.singleton (DirectEscape, absPath, sinkInstruction (nodeLabel sink)))) summ
        SinkFptr fsink ->
          let newVal = S.singleton (IndirectEscape, absPath, sinkInstruction (nodeLabel fsink))
          in (escapeFields ^!%= HM.insertWith S.union a newVal) summ
        SinkContract sink ->
          let newVal = S.singleton (BrokenContractEscape, absPath, sinkInstruction (nodeLabel sink))
          in (escapeFields ^!%= HM.insertWith S.union a newVal) summ
        SinkNone -> summ
    _ -> summ

-- A throwaway data type to encode the different types of escape sink
-- results from a search of the reached nodes.
data SinkType = SinkNormal EscapeNode
              | SinkFptr EscapeNode
              | SinkContract EscapeNode
              | SinkNone

sinkType :: [EscapeNode] -> SinkType
sinkType reached =
  case find nodeIsSink reached of
    Just sink -> SinkNormal sink
    Nothing ->
      case find nodeIsContractSink reached of
        Just sink -> SinkContract sink
        Nothing ->
          case find nodeIsFptrSink reached of
            Just fsink -> SinkFptr fsink
            Nothing -> SinkNone

-- | Given a query node and the sink it escaped to, determine the
-- shortest path between them in the escape graph and extract all of
-- the store instructions to be used as witnesses
storesInPath :: String -> EscapeNode -> EscapeNode -> EscapeGraph -> [Instruction]
storesInPath loc n sink g =
  mapMaybe isStore $ map (safeLab loc g) path
  where
    path = sp (const 1) (unlabelNode n) (unlabelNode sink) g

-- | A helper to abstract the pointer type tests.  If the value @v@ is
-- not a pointer, return @defVal@.  Otherwise, return @isPtrVal@.
-- This helps remove a level of nested (and repetitive) pattern
-- matching.
ifPointer :: IsValue v => v -> a -> a -> a
ifPointer v defVal isPtrVal =
  case valueType v of
    TypePointer _ _ -> isPtrVal
    _ -> defVal

-- | @reached@ is the list of nodes reachable from @v@.  If @v@ is not
-- in a loop in the escape graph, remove it from @reached@.  This is
-- necessary because the reaching computation considers @v@ to be
-- trivially reachable from itself and we don't want to count that as
-- an escape sink (unless it really does escape into itself).
removeValueIfNotInLoop :: IsValue v => v -> EscapeGraph -> [EscapeNode] -> [EscapeNode]
removeValueIfNotInLoop v g reached =
  case valueInLoop v g of
    True -> reached
    False -> filter ((/= valueUniqueId v) . unlabelNode) reached

-- | Return True if the given instruction is in a cycle in the use
-- graph
valueInLoop :: IsValue v => v -> EscapeGraph -> Bool
valueInLoop v g = any (valueInNonSingleton v) (scc g)
  where
    valueInNonSingleton val component =
      case length component > 1 of
        False -> False
        True -> valueUniqueId val `elem` component


isStore :: EscapeNode -> Maybe Instruction
isStore v =
  case nodeLabel v of
    InternalNode i _ ->
      case valueContent' i of
        InstructionC StoreInst {} -> Just i
        _ -> Nothing
    EscapeSink i ->
      case i of
        StoreInst {} -> Just i
        _ -> Nothing
    _ -> Nothing
{-

For each argument, remember which store instructions it is the value
of.  When we get to this stage, do a reachability computation from the
store address.  If it reaches a sink, take that store instruction as
the witness.

Collect *all* of the stores as witnesses
-}

nodeIsSink :: EscapeNode -> Bool
nodeIsSink t =
  case nodeLabel t of
    EscapeSink _ -> True
    ArgumentSource _ -> True
    FieldSource _ _ _ -> True
    _ -> False

nodeIsFptrSink :: EscapeNode -> Bool
nodeIsFptrSink t =
  case nodeLabel t of
    FptrSink _ -> True
    _ -> False

nodeIsContractSink :: EscapeNode -> Bool
nodeIsContractSink t =
  case nodeLabel t of
    ContractSink _ -> True
    _ -> False

nodeIsAnySink :: EscapeNode -> Bool
nodeIsAnySink t =
  case nodeLabel t of
    EscapeSink _ -> True
    FptrSink _ -> True
    WillEscapeSink _ -> True
    ArgumentSource _ -> True
    FieldSource _ _ _ -> True
    _ -> False

-- | Given the set of escapes via function call parameters (computed
-- in a preprocessing pass), construct the full escape graph.
--
-- This does a pass over the Function instructions to inspect
-- load/store instructions (along with a few others) to add nodes and
-- edges.
buildEscapeGraph :: CallEscapes -> Function -> EscapeGraph
buildEscapeGraph callEscapes f =
  mkGraph (uniqueNodes) (callEdges ++ escapeEdges)
  where
    argNodes = map toArgumentNode (functionParameters f)
    (bodyNodes, escapeEdges) = foldl' (collectEdges callEscapes) ([], []) (functionInstructions f)

    -- When making sinks for calls, *negate* the ID of the call
    -- instruction.  This will let instructions be both sources and
    -- sinks (which will be useful).
    (callArgNodes, callEdges) = buildCallEscapeSubgraph callEscapes
    allNodes = concat [ argNodes, callArgNodes, bodyNodes ]

    -- To unique the nodes, first sortBy on the node ID, then use
    -- groupBy on the same nodeid.  This will yield lists of lists;
    -- any list of length > 1 needs to be folded over to select the
    -- most specific node available (mostly discarding generic
    -- InternalNodes).  Edges do not need to be fixed at all since
    -- they are only keyed on ID
    uniqueNodes = uniqueEscapeGraphNodes allNodes

    toArgumentNode :: Argument -> EscapeNode
    toArgumentNode a = LNode (argumentUniqueId a) (ArgumentSource a)

-- | When generating nodes for instruction operands, we can sometimes
-- have more than one node for the same operand (e.g., if a value is
-- stored and used as a call argument, we'll generate a SinkNode for
-- the store and a possible sink node for the argument position).
--
-- This function chooses the most specific node for each value.  In
-- particular, this means that Sink nodes take precedence over all
-- (and fptr escapes take precedence over internal nodes).
uniqueEscapeGraphNodes :: [EscapeNode] -> [EscapeNode]
uniqueEscapeGraphNodes =
  foldr takeMostSpecificNodeForValue [] . doGroup . doSort
  where
    doGroup = groupBy ((==) `on` unlabelNode)
    doSort = sortBy (comparing unlabelNode)

    unique = S.toList . S.fromList

    takeMostSpecificNodeForValue :: [EscapeNode] -> [EscapeNode] -> [EscapeNode]
    takeMostSpecificNodeForValue ens acc =
      case ens of
        [] -> $failure "groupBy produced an empty group"
        [elt] -> elt : acc
        elts -> maximumBy escapeStrengthOrder (unique elts) : acc
      where
        -- Anything has higher precedence than an internal node.  Also,
        -- fptrescape can be superceded by any other sink.  Source nodes
        -- are superceded by sinks, though that should only happen for
        -- CallSource, but the call sinks have negated IDs
        escapeStrengthOrder nt1 nt2 =
          case (nodeLabel nt1, nodeLabel nt2) of
            (InternalNode _ _, InternalNode _ _) -> EQ
            (InternalNode _ _, _) -> LT
            (_, InternalNode _ _) -> GT
            (FptrSink _, FptrSink _) -> EQ
            (FptrSink _, _) -> LT
            (_, FptrSink _) -> GT
            _ -> $failure ("Unexpected escape order overlap " ++ show nt1 ++ " and " ++ show nt2)


-- | This helper needs to traverse valueEscapes and fptrEscapes and
-- make appropriate sink nodes (and edges).  fieldEscapes are taken
-- care of in the main function body traversal.  Note that the node
-- IDs of call sinks are negative to prevent collisions with real
-- nodes.
--
-- Note that each actual argument sink gets a unique (negative) ID.
-- The IDs are negative so that they do not conflict with any nodes
-- generated from the IR more directly.  They have to be unique per
-- actual so that an argument that escapes does not subsume another
-- pointer argument that only escapes via a function pointer (an
-- annotation of lesser severity).
buildCallEscapeSubgraph :: CallEscapes -> ([EscapeNode], [EscapeEdge])
buildCallEscapeSubgraph callEscapes = snd s0
  where
    -- The first element of the tuple is the list of unique IDs for
    -- escaping arguments.  Note that they are all negative.
    initVal = ([-1,-2..], ([], []))
    s0 = foldr makeCallEscape initVal $ HM.toList $ callEscapes ^. valueEscapes
    makeCallEscape (val, (tag, call)) (eid : rest, (ns, es)) =
      let constructor = case tag of
            DirectEscape -> EscapeSink
            BrokenContractEscape -> ContractSink
            IndirectEscape -> FptrSink
          newNode = LNode eid (constructor call)
          newEdge = LEdge (Edge (valueUniqueId val) eid) ()
      in (rest, (newNode : ns, newEdge : es))



-- | Build nodes and edges for the escape graph.  Note that we have a
-- very specific notion of escape here.  The following constructs
-- cause pointers to escape:
--
--  * ret instructions
--
--  * stores into arguments
--
--  * stores into globals
--
--  * stores into the return values of function calls
--
--  * passing a value as an argument that is known to escape
--
-- Note that we don't actually need to handle call instructions here
-- (except in that we need to create CallSource nodes for them) since
-- we have all of the relevant escape information bundled up in
-- @callEscapes@.  We can generate the necessary nodes and edges
-- directly from that much more easily.
collectEdges :: CallEscapes -> ([EscapeNode], [EscapeEdge])
                    -> Instruction -> ([EscapeNode], [EscapeEdge])
collectEdges callEscapes acc@(ns, es) i =
  case i of
    AllocaInst {} ->
      let newNode = toInternalNode i (Value i)
      in (newNode : ns, es)

    -- A return node gets a WillEscapeSink.  Only make this sink if
    -- the returned value is a pointer type (to keep graph sizes
    -- smaller)
    RetInst { retInstValue = Just rv } ->
      ifPointer rv acc $
        let newNode = LNode (instructionUniqueId i) (WillEscapeSink i)
            rnode = toInternalNode i rv
            e = LEdge (Edge (valueUniqueId rv) (instructionUniqueId i)) ()
        in (newNode : rnode : ns, e : es)

    -- This always returns a pointer
    GetElementPtrInst { getElementPtrValue = (valueContent' -> GlobalVariableC _) } ->
      let newNode = LNode (instructionUniqueId i) (EscapeSink i)
      in (newNode : ns, es)
    GetElementPtrInst { getElementPtrValue = (valueContent' -> ExternalValueC _) } ->
      let newNode = LNode (instructionUniqueId i) (EscapeSink i)
      in (newNode : ns, es)
    GetElementPtrInst { getElementPtrValue = (valueContent' -> ArgumentC _) } ->
      let newNode = LNode (instructionUniqueId i) (EscapeSink i)
      in (newNode : ns, es)
    GetElementPtrInst { getElementPtrValue = v } ->
      let newNode = toInternalNode i v
      in (newNode : ns, es)

    -- This is a load of a field of an argument (from a pointer to a
    -- struct).  These are important FieldSinks.  Note that argument
    -- sources are already in the graph so we don't need to make a new
    -- node for the argument.  There is no edge here yet.  Do not
    -- bother tracking non-pointer fields.
    LoadInst { loadAddress = (valueContent' -> InstructionC
      GetElementPtrInst { getElementPtrValue = (valueContent' -> ArgumentC a)})} ->
      ifPointer i acc $
        let Just apath = accessPath i
            absPath = abstractAccessPath apath
            newNode = LNode (instructionUniqueId i) (FieldSource a i absPath)
        in (newNode : ns, es)

    LoadInst { loadAddress = (valueContent' -> GlobalVariableC _) } ->
      ifPointer i acc $
        let newNode = LNode (valueUniqueId i) (EscapeSink i)
        in (newNode : ns, es)
    LoadInst { loadAddress = (valueContent' -> ExternalValueC _) } ->
      ifPointer i acc $
        let newNode = LNode (valueUniqueId i) (EscapeSink i)
        in (newNode : ns, es)
    LoadInst { loadAddress = (valueContent' -> ArgumentC _) } ->
      ifPointer i acc $
        let newNode = LNode (valueUniqueId i) (EscapeSink i)
        in (newNode : ns, es)
    LoadInst { loadAddress = la } ->
      ifPointer i acc $
        let newNode = toInternalNode i (Value i)
--            newEdge1 = LEdge (Edge (valueUniqueId la) (instructionUniqueId i)) ()
            newEdge2 = LEdge (Edge (instructionUniqueId i) (valueUniqueId la)) ()
        in (newNode : ns, newEdge2 : es)

    -- A store to a global generates a sink (the global) and an edge
    -- from the store value to the sink
    StoreInst { storeValue = sv, storeAddress = (valueContent' -> GlobalVariableC _) } ->
      ifPointer sv acc $
        let newNode = LNode (valueUniqueId i) (EscapeSink i)
            newEdge = LEdge (Edge (valueUniqueId sv) (valueUniqueId i)) ()
        in (newNode : ns, newEdge : es)
    StoreInst { storeValue = sv, storeAddress = (valueContent' -> ExternalValueC _) } ->
      ifPointer sv acc $
        let newNode = LNode (valueUniqueId i) (EscapeSink i)
            newEdge = LEdge (Edge (valueUniqueId sv) (valueUniqueId i)) ()
        in (newNode : ns, newEdge : es)
    StoreInst { storeValue = sv, storeAddress = (valueContent' -> ArgumentC _) } ->
      ifPointer sv acc $
        let newNode = LNode (valueUniqueId i) (EscapeSink i)
            newEdge = LEdge (Edge (valueUniqueId sv) (valueUniqueId i)) ()
        in (newNode : ns, newEdge : es)

{-
    -- In this case, we have a store to a field of a global (also an escape)
    StoreInst { storeValue = sv, storeAddress = (valueContent' -> InstructionC
      GetElementPtrInst { getElementPtrValue = (valueContent' -> GlobalVariableC _)})} ->
      ifPointer sv acc $
        let newNode = LNode (valueUniqueId i) (EscapeSink i)
            newEdge = LEdge (Edge (valueUniqueId sv) (valueUniqueId i)) ()
        in (newNode : ns, newEdge : es)
    StoreInst { storeValue = sv, storeAddress = (valueContent' -> InstructionC
      GetElementPtrInst { getElementPtrValue = (valueContent' -> ExternalValueC _)})} ->
      ifPointer sv acc $
        let newNode = LNode (valueUniqueId i) (EscapeSink i)
            newEdge = LEdge (Edge (valueUniqueId sv) (valueUniqueId i)) ()
        in (newNode : ns, newEdge : es)
    StoreInst { storeValue = sv, storeAddress = (valueContent' -> InstructionC
      GetElementPtrInst { getElementPtrValue = (valueContent' -> ArgumentC _)})} ->
      ifPointer sv acc $
        let newNode = LNode (valueUniqueId i) (EscapeSink i)
            newEdge = LEdge (Edge (valueUniqueId sv) (valueUniqueId i)) ()
        in (newNode : ns, newEdge : es)
-}

    -- Another interesting case is if the store address is a GEP whose
    -- base is in the callEscapes map (noted as escaping via function
    -- argument).  If the GEP points to one of the fields that
    -- escapes, this instruction generates a FieldSink node
    --
    -- This case handles all escapes via assignments to fields of
    -- structures that escape via function calls.
    --
    -- FIXME: If base is a global or argument, this can use a plain EscapeSink
    StoreInst { storeValue = sv, storeAddress = (valueContent' -> InstructionC
      GetElementPtrInst { getElementPtrValue = base })} ->
      ifPointer sv acc $
        case valueContent' base of
          ArgumentC _ ->
            let newNode = LNode (valueUniqueId i) (EscapeSink i)
                newEdge = LEdge (Edge (valueUniqueId sv) (valueUniqueId i)) ()
            in (newNode : ns, newEdge : es)
          GlobalVariableC _ ->
            let newNode = LNode (valueUniqueId i) (EscapeSink i)
                newEdge = LEdge (Edge (valueUniqueId sv) (valueUniqueId i)) ()
            in (newNode : ns, newEdge : es)
          ExternalValueC _ ->
            let newNode = LNode (valueUniqueId i) (EscapeSink i)
                newEdge = LEdge (Edge (valueUniqueId sv) (valueUniqueId i)) ()
            in (newNode : ns, newEdge : es)
          _ ->
            case HM.lookup base (callEscapes ^. fieldEscapes) of
              Nothing -> -- Just create an edge because this store into a
                        -- GEP doesn't escape here
                let newNode = toInternalNode i (Value i)
                    newEdge1 = LEdge (Edge (valueUniqueId sv) (valueUniqueId i)) ()
                    newEdge2 = LEdge (Edge (valueUniqueId i) (valueUniqueId base)) ()
                in (newNode : ns, newEdge1 : newEdge2 : es)
              Just paths ->
                let Just cpath = accessPath i
                    absPath = abstractAccessPath cpath
                in case absPath `elem` paths of
                  False ->
                    -- This field does *not* escape in a callee, so do
                    -- not add an edge (note, sv could still escape via
                    -- something else).
                    acc
                  True ->
                    -- This field being stored to escapes in a callee,
                    -- so the stored value escapes
                    let newNode = LNode (valueUniqueId i) (EscapeSink i)
                        newEdge = LEdge (Edge (valueUniqueId sv) (valueUniqueId i)) ()
                    in (newNode : ns, newEdge : es)

    -- Other stores add edges but not sinks.  Other sinks may become
    -- reachable.
    StoreInst { storeValue = sv, storeAddress = sa } ->
      ifPointer sv acc $
        -- FIXME: This probably needs a node for the address, but we
        -- have to be careful to allow that node to be superceded by
        -- a more specific type of node if we happen to find one.
        -- This will require post-processing at graph creation time
        -- to select the most specific node type with a given ID
        let newNode = toInternalNode i (Value i)
            newEdge1 = LEdge (Edge (valueUniqueId sv) (valueUniqueId i)) ()
            newEdge2 = LEdge (Edge (valueUniqueId i) (valueUniqueId sa)) ()
        in (newNode : ns, newEdge1 : newEdge2 : es)

    -- FIXME: We could treat PtrToInt casts as escaping, but that
    -- seems overly strict.  Maybe track all int types too?
    --
    -- PtrToIntInst {} -> undefined

    BitcastInst { castedValue = cv } ->
      let cn = toInternalNode i cv
          ino = toInternalNode i (Value i)
          e = toInternalEdge i cv
      in (cn : ino : ns, e : es)

    -- We have all of the call escape information in @callEscapes@, so
    -- we can more simply just traverse that to make the necessary
    -- edges and nodes.
    --
    -- Note, we use the un-negated ID here to treat call instructions
    -- as sources.  When treating them as escape sinks, negate the ID.
    CallInst {} ->
      ifPointer i acc $
        let newNode = LNode (valueUniqueId i) (EscapeSink i)
        in (newNode : ns, es)
    InvokeInst {} ->
      ifPointer i acc $
        let newNode = LNode (valueUniqueId i) (EscapeSink i)
        in (newNode : ns, es)

    -- Instructions representing more than one value get their own
    -- node with an edge from each of their possible values.
    SelectInst { selectTrueValue = tv, selectFalseValue = fv } ->
      ifPointer i acc $
        let tn = toInternalNode i tv
            fn = toInternalNode i fv
            te = toInternalEdge i tv
            fe = toInternalEdge i fv
        in (tn : fn : ns, te : fe : es)
    PhiNode { phiIncomingValues = ivs } ->
      ifPointer i acc $
        let newNode = toInternalNode i (Value i)
            newEdges = map (toInternalEdge i) (map fst ivs)
        in (newNode : ns, newEdges ++ es)

    -- InsertElementInst {} -> undefined
    -- InsertValueInst {} -> undefined
    _ -> acc


toInternalNode :: Instruction -> Value -> EscapeNode
toInternalNode i v = LNode (valueUniqueId v) (InternalNode i v)

toInternalEdge :: (IsValue a, IsValue b) => a -> b -> EscapeEdge
toInternalEdge i v = LEdge (Edge (valueUniqueId v) (valueUniqueId i)) ()

-- | This is the pre-processing pass that builds the 'CallEscapes' summary for
-- the function.  That is, it identifies all of the values used in argument
-- positions to calls that escape (or may escape via function pointer).
--
-- FIXME: It could increase precision to add another parameter
--
-- > (ExternalFunction -> Int -> m [AbstractAccessPath]
--
-- To summarize the field escapes of external functions.  This is
-- unlikely to be particularly useful, since most complicated
-- relationships like that would be mostly restricted to the internals
-- of a library
buildEscapeMaps :: (Monad m) => (ExternalFunction -> Int -> m Bool)
                   -> EscapeSummary -> IndirectCallSummary
                   -> CallEscapes -> Instruction -> m CallEscapes
buildEscapeMaps extSumm summ ics acc i =
  case i of
    CallInst { callFunction = f, callArguments = args } ->
      collectEscapes extSumm summ ics i acc f (map fst args)
    InvokeInst { invokeFunction = f, invokeArguments = args } ->
      collectEscapes extSumm summ ics i acc f (map fst args)
    _ -> return acc

-- | The real worker that determines the escape properties of each
-- actual argument based on what functions might be called by this
-- instruction.
collectEscapes :: (Monad m) => (ExternalFunction -> Int -> m Bool) -> EscapeSummary
                  -> IndirectCallSummary -> Instruction
                  -> CallEscapes -> Value -> [Value] -> m CallEscapes
collectEscapes extSumm summ ics ci ces callee args =
  case valueContent' callee of
    -- Use the external summary function to check each argument
    ExternalFunctionC ef -> foldM (checkExt ef) ces (zip [0..] args)

    -- Use the internal summary (EscapeResult) to figure out what
    -- arguments are doing in a more granular way (including field
    -- escapes)
    FunctionC f ->
      let formals = functionParameters f
      in return $! foldl' (checkFuncArg summ ci) ces (zip formals args)

    -- This is a call through a function pointer, and all of its
    -- arguments have fptr-escape.
    _ ->
      case consistentTargetEscapes summ ics ci of
        Nothing -> return $ foldr (\arg -> valueEscapes ^!%= HM.insert arg (IndirectEscape, ci)) ces args
        Just representative ->
          let formals = functionParameters representative
          in return $! foldl' (checkContractFuncArg summ ci) ces (zip formals args)
  where
    checkExt ef acc (ix, arg) = do
      doesEscape <- extSumm ef ix
      case doesEscape of
        False -> return acc
        True -> return $! (valueEscapes ^!%= HM.insert arg (DirectEscape, ci)) acc

-- | If all of the resolvable targets of the given call/invoke
-- instruction have the same escape properties for each argument,
-- return an arbitrary one as a representative for the analysis.
consistentTargetEscapes :: EscapeSummary -> IndirectCallSummary -> Instruction -> Maybe Function
consistentTargetEscapes summ ics ci = do
  fs <- nonEmpty targets -- `debug` printf "targets for <%s>: %s (from %s)\n" (show ci) (show targets) (show ics)
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

checkContractFuncArg :: EscapeSummary -> Instruction -> CallEscapes -> (Argument, Value) -> CallEscapes
checkContractFuncArg summ ci ces (formal, arg)
  | not (isPointerValue arg) = ces
  | otherwise =
    case HM.lookup formal (summ ^. escapeArguments) of
      Nothing -> (valueEscapes ^!%= HM.insert arg (BrokenContractEscape, ci)) ces -- `debug` ("n " ++ show summ)
      Just (esctype, _) -> (valueEscapes ^!%= HM.insert arg (esctype, ci)) ces -- `debug` ("j " ++ show summ)

-- | Check these in order because there is a superceding relationship
-- here.  General escapes take precedence over field escapes, which in
-- turn take precedence over fptr escapes.
checkFuncArg :: EscapeSummary -> Instruction -> CallEscapes -> (Argument, Value) -> CallEscapes
checkFuncArg summ ci ces (formal, arg)
  | not (isPointerValue arg) = ces
  | otherwise =
    case HM.lookup formal (summ ^. escapeArguments) of
      Just (DirectEscape, _) -> (valueEscapes ^!%= HM.insert arg (DirectEscape, ci)) ces
      _ -> case HM.lookup formal (summ ^. escapeFields) of
        Just apsAndWitnesses ->
          let aps = S.toList $ S.map (\(_, fld, _) -> fld) apsAndWitnesses
          in (fieldEscapes ^!%= HM.insertWith (++) arg aps) ces
        Nothing -> case HM.lookup formal (summ ^. escapeArguments) of
          Just (IndirectEscape, _) -> (valueEscapes ^!%= HM.insert arg (IndirectEscape, ci)) ces
          _ -> ces


isPointerValue :: (IsValue a) => a -> Bool
isPointerValue v =
  case valueType v of
    TypePointer _ _ -> True
    _ -> False

safeLab :: String -> EscapeGraph -> Int -> EscapeNode
safeLab loc g n =
  case lab g n of
    Nothing -> error (loc ++ ": missing label for use graph node")
    Just l -> LNode n l

-- Testing

-- | Extract the arguments for each function that escape.  The keys of
-- the map are function names and the set elements are argument names.
-- This format exposes the internal results for testing purposes.
--
-- For actual use in a program, use one of 'functionEscapeArguments',
-- 'functionWillEscapeArguments', or 'instructionEscapes' instead.
escapeResultToTestFormat :: EscapeSummary -> Map String (Set (EscapeClass, String))
escapeResultToTestFormat er =
  foldr fieldTransform directEscapes (HM.toList fm)
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


-- | The same as 'escapeResultToTestFormat', but for the willEscape
-- arguments.
-- willEscapeResultToTestFormat :: EscapeResult -> Map String (Set String)
-- willEscapeResultToTestFormat er = undefined
{-
  foldr transform Map.empty (HM.keys m)
  where
    m = willEscapeArguments er
    transform a acc =
      let f = argumentFunction a
          fname = show (functionName f)
          aname = show (argumentName a)
      in Map.insertWith' S.union fname (S.singleton aname) acc
-}


escapeUseGraphs :: EscapeSummary -> [(String, EscapeGraph)]
escapeUseGraphs = map (first (show . functionName)) . HM.toList . (^. escapeGraphs)

useGraphvizParams :: GraphvizParams n NodeType el () NodeType
useGraphvizParams =
  nonClusteredParams { fmtNode = \(_, l) -> [toLabel l]
                     , fmtEdge = \_ -> []
                     }

useGraphvizRepr :: EscapeGraph -> DotGraph Int
useGraphvizRepr g = graphElemsToDot useGraphvizParams ns es
  where
    ns = map toNodeTuple $ labNodes g
    es = map toEdgeTuple $ labEdges g
