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
import Control.Exception ( throw )
import Control.Monad.Writer ( runWriter )
import Data.Default
import Data.Hashable
import Data.HashMap.Strict ( HashMap )
import qualified Data.HashMap.Strict as HM
import Data.List ( transpose )
import Data.List.NonEmpty ( NonEmpty, nonEmpty )
import qualified Data.List.NonEmpty as NEL
import Data.Map ( Map )
import qualified Data.Map as M
import Data.Maybe ( mapMaybe )
import Data.Set ( Set )
import qualified Data.Set as S
import Data.Lens.Common
import Data.Lens.Template
import Data.Monoid
import Text.Printf

import Database.Datalog
import LLVM.Analysis
import LLVM.Analysis.AccessPath
import LLVM.Analysis.CallGraphSCCTraversal

import Foreign.Inference.Diagnostics
import Foreign.Inference.Interface
import Foreign.Inference.Analysis.IndirectCallResolver

data Fact = W Instruction -- witness
          | EscapeSink EscapeClass Value
          | FieldSource Argument AbstractAccessPath
          | P AbstractAccessPath
          | V Value -- a value
          deriving (Eq, Ord, Show)

instance Hashable Fact where
  hash (W i) = 1 `combine` hash i
  hash (EscapeSink ec v) = 2 `combine` hash v `combine` hash ec
  hash (V v) = 3 `combine` hash v
  hash (FieldSource a p) = 4 `combine` hash a `combine` hash p
  hash (P p) = 5 `combine` hash p

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

data EscapeSummary =
  EscapeSummary { _escapeData :: HashMap Function (Database Fact)
                , _escapeArguments :: HashMap Argument (EscapeClass, Instruction)
                , _escapeFields :: HashMap Argument (Set (EscapeClass, AbstractAccessPath, Instruction))
                , _escapeDiagnostics :: Diagnostics
                }

$(makeLens ''EscapeSummary)

instance Show EscapeSummary where
  show (EscapeSummary _ ea ef _) = show ea ++ "/" ++ show ef

instance Eq EscapeSummary where
  (EscapeSummary db1 ea1 ef1 _) == (EscapeSummary db2 ea2 ef2 _) =
    db1 == db2 && ea1 == ea2 && ef1 == ef2

instance Default EscapeSummary where
  def = EscapeSummary mempty mempty mempty mempty

instance Monoid EscapeSummary where
  mempty = def
  mappend (EscapeSummary db1 as1 was1 d1) (EscapeSummary db2 as2 was2 d2) =
    EscapeSummary { _escapeData = HM.union db1 db2
                  , _escapeArguments = HM.union as1 as2
                  , _escapeFields = HM.union was1 was2
                  , _escapeDiagnostics = d1 `mappend` d2
                  }

-- We don't need to rnf the fact database because it is queried to
-- create the argument summaries (and is therefore fully evaluated).
instance NFData EscapeSummary where
  rnf r@(EscapeSummary _ as was d) =
    as `deepseq` was `deepseq` d `deepseq` r `seq` ()

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
                   -> Lens compositeSummary EscapeSummary
                   -> ComposableAnalysis compositeSummary funcLike
identifyEscapes ds ics lns =
  composableAnalysisM runner escapeWrapper lns
  where
    escapeWrapper funcLike s = do
      let f = getFunction funcLike
          db = either throwDatalogError id $
                 makeDatabase $ collectFacts ics extSumm s (functionInstructions f)
          res = either throwDatalogError id $ queryDatabase db (escapeQuery Nothing Nothing)
          s' = foldr summarizeArgumentEscapes s res
      return $ (escapeData ^!%= HM.insert f db) s'
-- FIXME: It might be worth changing the query here to issue a single
-- query for each argument.  The field escape stuff would make that
-- hard, though.

    runner a =
      let (e, diags) = runWriter a
      in (escapeDiagnostics ^= diags) e

    extSumm ef ix =
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
instructionEscapeCore ignorePred i (EscapeSummary dbs _ _ _) =
  foldr (matchInst i) Nothing res
  where
    Just bb = instructionBasicBlock i
    f = basicBlockFunction bb
    errMsg = error ("Should have a summary for " ++ show (functionName f))
    db = HM.lookupDefault errMsg f dbs
    q = queryDatabase db (escapeQuery (Just ignorePred) (Just (Atom (V (toValue i)))))
    res = either throwDatalogError id q

matchInst :: Instruction -> [Fact] -> Maybe Instruction -> Maybe Instruction
matchInst _ _ res@(Just _) = res
matchInst i [V v, _, W w, _] Nothing =
  case valueUniqueId v == instructionUniqueId i of
    False -> Nothing
    True -> Just w
matchInst _ _ _ = Nothing


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

-- FIXME: Now we can encounter the same argument more than once while
-- going through the results.  Use a smart merge to make sure direct
-- escapes override indirect &c.
summarizeArgumentEscapes :: [Fact] -> EscapeSummary -> EscapeSummary
summarizeArgumentEscapes [V _, EscapeSink ec _, W w, FieldSource a accPath] =
  escapeFields ^!%= HM.insertWith S.union a (S.singleton (ec, accPath, w))
summarizeArgumentEscapes [V v, EscapeSink ec _, W w, _] =
  case valueContent' v of
    ArgumentC a -> escapeArguments ^!%= HM.insert a (ec, w)
    _ -> id
summarizeArgumentEscapes _ = id

collectFacts :: (Failure DatalogError m)
                => IndirectCallSummary
                -> (ExternalFunction -> Int -> Bool)
                -> EscapeSummary
                -> [Instruction]
                -> DatabaseBuilder m Fact ()
collectFacts ics extSumm summ is = do
  sink <- addRelation "sink" 2
  flowTo <- addRelation "flowTo" 3
  fieldSource <- addRelation "fieldSource" 2
  fieldStore <- addRelation "fieldStore" 4
  callFieldEscape <- addRelation "callFieldEscape" 4
  mapM_ (addFact ics extSumm summ sink flowTo fieldSource fieldStore callFieldEscape) is


-- FIXME if we can identify function call arguments as sinks here, that
-- could save significant complexity later
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

escapeQuery :: (Failure DatalogError m)
               => Maybe (Instruction -> Bool)
               -> Maybe (Term Fact)
               -> QueryBuilder m Fact (Query Fact)
escapeQuery ignorePred target = do
  sink <- relationPredicateFromName "sink"
  flowTo <- relationPredicateFromName "flowTo"
  fieldSource <- relationPredicateFromName "fieldSource"
  flowTo' <- inferencePredicate "flowTo*"
  escapes <- inferencePredicate "escapes"
  fieldStore <- relationPredicateFromName "fieldStore"
  callFieldEscape <- relationPredicateFromName "callFieldEscape"
  let v = LogicVar "v"
      s = LogicVar "s"
      w = LogicVar "w"
      v1 = LogicVar "v1"
      v2 = LogicVar "v2"
      w2 = LogicVar "w2"
      f = LogicVar "f"
      p = LogicVar "p"
      base = LogicVar "base"
  -- Graph closure
  case ignorePred of
    Nothing -> (flowTo', [v, s, w]) |- [ lit flowTo [ v, s, w ] ]
    Just ignore ->
      (flowTo', [v, s, w]) |- [ lit flowTo [ v, s, w ]
                              , cond1 (\(W inst) -> not (ignore inst)) w
                              ]
  (flowTo', [v, v2, w]) |- [ lit flowTo' [ v, v1, Anything ]
                           , lit flowTo' [ v1, v2, w ]
                           ]
  -- Final query

  -- This rule handles proxying field escapes through callees.  See
  -- escape-through-2-call-field.c
  (escapes, [v, s, w, p]) |- [ lit callFieldEscape [ v, Anything, s, w ]
                             , lit fieldSource [ v, p ]
                             ]

  -- In this case, the w2 parameter is fake and unused, but we want
  -- this to be arity 3 so that we can handle field escapes in the
  -- same query.  This simple case says that anything reaching a sink
  -- node escapes (directly).
  (escapes, [v, s, w, w2]) |- [ lit flowTo' [ v, s, w2 ]
                              , lit sink [ s, w ]
                              ]

  -- This case describes fields of arguments escaping (directly)
  (escapes, [v, s, w, f]) |- [ lit flowTo' [ v, s, Anything ]
                             , lit sink [ s, w ]
                             , lit fieldSource [ v, f ]
                             ]

  -- This case handles fields of values escaping through calls
  (escapes, [v, s, w, p]) |- [ lit flowTo' [ v, v2, Anything ]
                             , lit fieldStore [ base, v2, p, Anything ]
                             , lit callFieldEscape [ base, p, s, w ]
                             ]
  -- There isn't necessarily an extra flow step here since a value
  -- could escape directly... this works but we might be able to
  -- combine the rules if we are more clever.
  (escapes, [v, s, w, p]) |- [ lit fieldStore [ base, v, p, Anything ]
                             , lit callFieldEscape [ base, p, s, w ]
                             ]
  case target of
    Nothing -> issueQuery escapes [ v, s, w, f ]
    Just tgt -> issueQuery escapes [ tgt, s, w, f]

-- | A helper to abstract the pointer type tests.  If the value @v@ is
-- not a pointer, return @defVal@.  Otherwise, return @isPtrVal@.
-- This helps remove a level of nested (and repetitive) pattern
-- matching.
ifPointer :: IsValue v => v -> a -> a -> a
ifPointer v defVal isPtrVal =
  case valueType v of
    TypePointer _ _ -> isPtrVal
    _ -> defVal


-- FIXME at a high level, I need to add many more tests to ensure that
-- escapes by address-taken operations are handled properly.
addFact :: (Failure DatalogError m)
           => IndirectCallSummary
           -> (ExternalFunction -> Int -> Bool)
           -> EscapeSummary
           -> Relation
           -> Relation
           -> Relation
           -> Relation
           -> Relation
           -> Instruction
           -> DatabaseBuilder m Fact ()
addFact ics extSumm summ sink flowTo fieldSource fieldStore callFieldEscape inst =
  case inst of
    RetInst { retInstValue = Just rv } ->
      ifPointer rv (return ()) $ do
        let s = EscapeSink DirectEscape rv
        assertFact sink [ s, W inst ]
        assertFact flowTo [ V rv, s, W inst ]

    GetElementPtrInst { getElementPtrValue = base } ->
      assertFact flowTo [ V (toValue inst), V base, W inst ]

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
              let s = FieldSource a (abstractAccessPath cpath)
              assertFact fieldSource [ V (toValue inst), s ]
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
          assertFact flowTo [ V sv, V sa, W inst ]
          case (base, absPath) of
            (Just b, Just absPath') ->
              assertFact fieldStore [ V b, V sv, P absPath', W inst ]
            _ -> return ()
              -- At call sites where a field escapes, assert the fact:
              --
              -- > assertFact fieldEscapeSink [ V base, P absPath, W inst ]
              --
              -- and then match them up on base/path in a secondary
              -- escape rule (sv escapes via inst),
        True -> do
          let s = EscapeSink DirectEscape sa
          assertFact sink [ s, W inst ]
          assertFact flowTo [ V sv, s, W inst ]
    CallInst { callFunction = f, callArguments = args } -> do
      addCallArgumentFacts ics extSumm summ sink flowTo callFieldEscape fieldSource inst f (map fst args)
      -- If the function call returns a pointer, that pointer is an
      -- escape sink (assigning a pointer to it lets that pointer
      -- escape since it could be a global pointer).
      ifPointer inst (return ()) $ do
        assertFact sink [ EscapeSink DirectEscape (toValue inst), W inst ]
    InvokeInst { invokeFunction = f, invokeArguments = args } -> do
      addCallArgumentFacts ics extSumm summ sink flowTo callFieldEscape fieldSource inst f (map fst args)
      ifPointer inst (return ()) $ do
        assertFact sink [ EscapeSink DirectEscape (toValue inst), W inst ]
    PhiNode { phiIncomingValues = ivs } ->
      mapM_ (\v -> assertFact flowTo [ V v, V (toValue inst), W inst ]) (map fst ivs)
    SelectInst { selectTrueValue = tv, selectFalseValue = fv } -> do
      assertFact flowTo [ V tv, V (toValue inst), W inst ]
      assertFact flowTo [ V fv, V (toValue inst), W inst ]
    BitcastInst { castedValue = cv } ->
      assertFact flowTo [ V cv, V (toValue inst), W inst ]
    _ -> return ()

addCallArgumentFacts :: (Failure DatalogError m)
                        => IndirectCallSummary
                        -> (ExternalFunction -> Int -> Bool)
                        -> EscapeSummary
                        -> Relation
                        -> Relation
                        -> Relation
                        -> Relation
                        -> Instruction
                        -> Value
                        -> [Value]
                        -> DatabaseBuilder m Fact ()
addCallArgumentFacts ics extSumm summ sink flowTo callFieldEscape fieldSource ci callee args =
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
    doAssert etype v = do
      let s = EscapeSink etype (toValue ci)
      assertFact sink [ s, W ci ]
      assertFact flowTo [ V v, s, W ci ]
    argFieldAssert etype v absPath = do
              --       let s = FieldSource a (abstractAccessPath cpath)
              -- assertFact fieldSource [ V (toValue inst), s ]

      let s = EscapeSink etype (toValue ci)
      assertFact sink [ s, W ci ]
--      assertFact flowTo [ V v, s, W ci ]
      assertFact callFieldEscape [ V v, P absPath, s, W ci ]
      case valueContent' v of
        ArgumentC a -> do
          let src = FieldSource a absPath
--          assertFact flowTo [ V v, src, W ci ]
          assertFact fieldSource [ V v, src ]
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

-- Helpers

-- This is a trivial function to constrain the type of 'throw' so that
-- Failure DatalogError (Either a) can be recognized as Failure
-- DatalogError (Either DatalogError) and pick up the Failure instance
throwDatalogError :: DatalogError -> a
throwDatalogError = throw


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
