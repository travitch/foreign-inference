{-# LANGUAGE ViewPatterns, RankNTypes, ScopedTypeVariables #-}
{-# LANGUAGE DeriveGeneric, TemplateHaskell #-}
module Foreign.Inference.Analysis.ErrorHandling (
  ErrorSummary,
  identifyErrorHandling,
  -- * Testing
  -- allocatorSummaryToTestFormat
  ) where

import GHC.Generics

import Control.DeepSeq
import Control.DeepSeq.Generics ( genericRnf )
import Control.Lens ( Simple, (%~), (.~), makeLenses )
import Control.Monad ( foldM, when )
import Control.Monad.Trans.Class
import Control.Monad.Trans.Maybe
import qualified Data.Foldable as F
import Data.HashMap.Strict ( HashMap )
import qualified Data.HashMap.Strict as HM
import Data.IntMap ( IntMap )
import qualified Data.IntMap as IM
import Data.List ( elemIndex )
import qualified Data.List.NonEmpty as NEL
import Data.Monoid
import Data.SBV
import Data.Set ( Set )
import qualified Data.Set as S
import System.IO.Unsafe ( unsafePerformIO )

import LLVM.Analysis
import LLVM.Analysis.BlockReturnValue
import LLVM.Analysis.CallGraphSCCTraversal
import LLVM.Analysis.CDG
import LLVM.Analysis.CFG
import LLVM.Analysis.Dominance

import Foreign.Inference.AnalysisMonad
import Foreign.Inference.Diagnostics
import Foreign.Inference.Interface
import Foreign.Inference.Internal.FlattenValue
import Foreign.Inference.Analysis.IndirectCallResolver

-- import Text.Printf
-- import Debug.Trace
-- debug :: a -> String -> a
-- debug = flip trace

type ErrorDescriptor = (Set ErrorAction, [Witness])
type SummaryType = HashMap Function (Set ErrorDescriptor)
data ErrorSummary =
  ErrorSummary { _errorSummary :: SummaryType
               , _errorDiagnostics :: Diagnostics
               }
  deriving (Generic)

$(makeLenses ''ErrorSummary)

instance Eq ErrorSummary where
  (ErrorSummary s1 _) == (ErrorSummary s2 _) = s1 == s2

instance Monoid ErrorSummary where
  mempty = ErrorSummary mempty mempty
  mappend (ErrorSummary m1 d1) (ErrorSummary m2 d2) =
    ErrorSummary (HM.union m1 m2) (mappend d1 d2)

instance NFData ErrorSummary where
  rnf = genericRnf

instance HasDiagnostics ErrorSummary where
  diagnosticLens = errorDiagnostics

-- | Take an ErrorSummary and extract the list of error handling
-- patterns.  Assume that each function only reports errors in a
-- single way and then find the common error reporting code used by
-- each function.  After that, the resolution strategy comes in and
-- perhaps even optimization.
distillSummary :: ErrorSummary -> [ErrorDescriptor]
distillSummary (ErrorSummary s _) =
  case NEL.nonEmpty (HM.toList s) of
    Nothing -> []
    Just hdlrs ->
      let funcErrorHandlers = fmap unifyErrorHandler hdlrs
      in F.foldr mergeIdenticalHandlers mempty funcErrorHandlers

-- This filter is kind of a bad idea.  It is applied to the seed value
-- after an initial analysis of the module and is used to combine the
-- initial error handling patterns and remove redundant ones.
--
-- The problem is that, for libraries that return only error codes
-- (and don't take additional actions), this discards everything.
-- What we want to do are remove singleton -1 and 0 returns at most.

-- Another problem is that unifyErrorHandlers assumes only one method
-- is used to report errors.  This is sort of fine, except outliers
-- need to be thrown away.  For example, some functions return -1 as a
-- default, but return -1 and call an error function when real errors
-- occur.  Currently, unifyErrorHandlers unifies them all into
-- "returns -1", which is not useful or really correct.  The filter
-- should be applied inside of unifyErrorHandlers (and if unification
-- fails after that, revert the filter).

mergeIdenticalHandlers :: (Eq a) => a -> [a] -> [a]
mergeIdenticalHandlers h acc =
  case F.find (==h) acc of
    Nothing -> h : acc
    Just _ -> acc

-- A better approach here might be to (for now) just unify the
-- descriptors that will unify and leave the rest?  Basically try to
-- unify each new descriptor with the current ones and, if it doesn't
-- unify, add it as a new error handling pattern.
--
-- The representation of this will be important.  It isn't a prefix or
-- suffix tree - it is a set of possibly disconnected DAGs.
--
-- For now, collect all descriptors unifying those that unify
-- trivially.

-- | Unify the error handling patterns found *within* the given function.
-- | Note, this uses foldr1 but each set cannot be empty (since we use
-- insertWith below, we can't have empty sets).
unifyErrorHandler :: (Function, Set ErrorDescriptor) -> ErrorDescriptor
unifyErrorHandler (_, s) =
  if S.null complexPatterns then F.foldr1 combineHandler s -- unifiedComplex
  else unifiedComplex
  where
    unifiedComplex = F.foldr1 combineHandler complexPatterns
    complexPatterns = S.filter ((>1) . S.size . fst) s
--    h = F.foldr1 combineHandler s

-- | For each action in the first set, find a corresponding action in
-- the second set.  If there is a match, find the common part they
-- share and insert it into the result.  Otherwise, discard it.
--
-- We can just discard witnesses here since the second pass will
-- re-capture them
combineHandler :: ErrorDescriptor -> ErrorDescriptor -> ErrorDescriptor
combineHandler (d0, _) (other, _) = (dN, [])
  where
    dN = snd $ F.foldr findCorresponding (d0, mempty) other
    findCorresponding act (targets, acc) =
      case F.foldr (unifyErrorAction act) Nothing targets of
        Nothing -> (targets, acc)
        Just (act', t) ->
          (S.delete t targets, S.insert act' acc)
-- FIXME: Discard outlier error actions when combining the error actions
-- for a single function

unifyErrorAction :: ErrorAction
                    -> ErrorAction
                    -> Maybe (ErrorAction, ErrorAction)
                    -> Maybe (ErrorAction, ErrorAction)
unifyErrorAction _ _ j@(Just _) = j
unifyErrorAction a1 a2 Nothing =
  case (a1, a2) of
    (ReturnConstantInt s1, ReturnConstantInt s2) ->
      return (ReturnConstantInt (s1 `S.union` s2), a2)
    (ReturnConstantPtr s1, ReturnConstantPtr s2) ->
      return (ReturnConstantPtr (s1 `S.union` s2), a2)
    (AssignToGlobal g1 s1, AssignToGlobal g2 s2) ->
      case g1 == g2 of
        False -> Nothing
        True -> return (AssignToGlobal g1 (s1 `S.union` s2), a2)
    (AssignToCall c1 s1, AssignToCall c2 s2) ->
      case c1 == c2 of
        False -> Nothing
        True -> return (AssignToCall c1 (s1 `S.union` s2), a2)
    (FunctionCall f1 args1, FunctionCall f2 args2) ->
      case f1 == f2 of
        False -> Nothing
        -- FIXME: Merge arguments.  Maybe change args to be
        -- represented with an IntMap and use intersectionWith
        True -> return (FunctionCall f1 mempty, a2)
    _ -> Nothing

data ErrorData =
  ErrorData { dependencySummary :: DependencySummary
            , _blockRetLabels :: BlockReturns
            , indirectCallSummary :: IndirectCallSummary
            , errorSeed :: [ErrorDescriptor]
            }

$(makeLenses ''ErrorData)

type Analysis = AnalysisMonad ErrorData ()

instance SummarizeModule ErrorSummary where
  summarizeArgument _ _ = []
  summarizeFunction f (ErrorSummary summ _) =
    case HM.lookup f summ of
      Nothing -> []
      Just s ->
        case NEL.nonEmpty (F.toList s) of
          Nothing -> []
          Just descs ->
            let (acts, _) = F.foldr1 combineHandler descs
                ws = concat $ map snd (NEL.toList descs)
            in [(FAReportsErrors acts, ws)]

identifyErrorHandling :: forall compositeSummary funcLike . (FuncLike funcLike, HasFunction funcLike, HasCDG funcLike, HasPostdomTree funcLike, HasCFG funcLike)
                         => Module
                         -> DependencySummary
                         -> IndirectCallSummary
                         -> Simple Lens compositeSummary ErrorSummary
                         -> ComposableAnalysis compositeSummary funcLike
identifyErrorHandling m ds ics =
  composableAnalysisM runner errorAnalysis
  where
    runner a = runAnalysis a readOnlyData ()
    readOnlyData = ErrorData ds mempty ics (distillSummary seed)

    funcLikes :: [funcLike]
    funcLikes = map fromFunction (moduleDefinedFunctions m)
    analysis0 = foldM (flip errorAnalysis) mempty funcLikes
    readOnly0 = ErrorData ds mempty ics mempty
    seed = runAnalysis analysis0 readOnly0 ()

-- | Find each function call for which we have an error descriptor.
-- Then find the branch handling the error (if there is one) and add
-- that summary to the ErrorSummary for this function.
--
-- Look for br (cmp (call)) patterns
errorAnalysis :: (FuncLike funcLike, HasFunction funcLike, HasCDG funcLike, HasPostdomTree funcLike, HasCFG funcLike)
                 => funcLike
                 -> ErrorSummary
                 -> Analysis ErrorSummary
errorAnalysis funcLike s =
  analysisLocal (blockRetLabels .~ retLabels) $
    foldM (analyzeErrorChecks f) s (functionBody f) -- `debug` ("Analyzing function " ++ show (functionName f))
  where
    f = getFunction funcLike
    retLabels = labelBlockReturns funcLike

analyzeErrorChecks :: Function
                      -> ErrorSummary
                      -> BasicBlock
                      -> Analysis ErrorSummary
analyzeErrorChecks f s bb = do
  takeFirst s [ handlesKnownError f s bb
              , executesLearnedErrorPattern f s bb
              , returnsTransitiveError f s
              ]

takeFirst :: (Monad m) => a -> [m (Maybe a)] -> m a
takeFirst def [] = return def
takeFirst def (act:rest) = do
  res <- act
  maybe (takeFirst def rest) return res

returnsTransitiveError :: Function -> ErrorSummary -> Analysis (Maybe ErrorSummary)
returnsTransitiveError f s = do
  ds <- analysisEnvironment dependencySummary
  ics <- analysisEnvironment indirectCallSummary
  return $ do
    exitInst <- functionExitInstruction f
    case exitInst of
      RetInst { retInstValue = Just rv } ->
        let rvs = flattenValue rv
        in foldr (checkTransitiveError ics ds s f) Nothing rvs
      _ -> Nothing

checkTransitiveError :: IndirectCallSummary
                        -> DependencySummary
                        -> ErrorSummary
                        -> Function
                        -> Value
                        -> Maybe ErrorSummary
                        -> Maybe ErrorSummary
checkTransitiveError _ _ _ _ _ j@(Just _) = j
checkTransitiveError ics ds s f rv Nothing =
  case valueContent' rv of
    InstructionC i@CallInst { callFunction = callee } ->
      let callees = callTargets ics callee
      in foldr (recordTransitiveError f ds s i) Nothing callees
    _ -> Nothing

recordTransitiveError :: Function -> DependencySummary -> ErrorSummary
                         -> Instruction -> Value -> Maybe ErrorSummary
                         -> Maybe ErrorSummary
recordTransitiveError _ _ _ _ _ j@(Just _) = j
recordTransitiveError f ds s i callee Nothing = do
  summ <- lookupFunctionSummary ds s callee
  FAReportsErrors errActs <- F.find isErrRetAnnot summ
  let w = Witness i "transitive error"
      upd = errorSummary %~ HM.insertWith S.union f (S.singleton (errActs, [w]))
  return $ upd s

callTargets :: IndirectCallSummary -> Value -> [Value]
callTargets ics callee =
  case valueContent' callee of
    FunctionC _ -> [callee]
    ExternalFunctionC _ -> [callee]
    _ -> indirectCallInitializers ics callee

isErrRetAnnot :: FuncAnnotation -> Bool
isErrRetAnnot (FAReportsErrors _) = True
isErrRetAnnot _ = False

handlesKnownError :: Function
                     -> ErrorSummary
                     -> BasicBlock
                     -> Analysis (Maybe ErrorSummary)
handlesKnownError f s bb =
  case basicBlockTerminatorInstruction bb of
    bi@BranchInst { branchCondition = (valueContent' ->
      InstructionC ci@ICmpInst { cmpPredicate = p
                               , cmpV1 = v1
                               , cmpV2 = v2
                               })
               , branchTrueTarget = tt
               , branchFalseTarget = ft
               } -> runMaybeT $ do
      errDesc <- extractErrorHandlingCode f s p v1 v2 tt ft
      let w1 = Witness ci "check error return"
          w2 = Witness bi "return error code"
          upd = errorSummary %~ HM.insertWith S.union f (S.singleton (errDesc, [w1,w2]))
      return $ upd s
    _ -> return Nothing

executesLearnedErrorPattern :: Function
                               -> ErrorSummary
                               -> BasicBlock
                               -> Analysis (Maybe ErrorSummary)
executesLearnedErrorPattern f s bb = do
  brs <- analysisEnvironment _blockRetLabels
  errStyles <- analysisEnvironment errorSeed
  return $ do
    bret <- blockReturn brs bb
    foldr (checkLearnedStyle f bb bret s) Nothing errStyles

checkLearnedStyle :: Function
                     -> BasicBlock
                     -> Value
                     -> ErrorSummary
                     -> ErrorDescriptor
                     -> Maybe ErrorSummary
                     -> Maybe ErrorSummary
checkLearnedStyle _ _ _ _ _ r@(Just _) = r
checkLearnedStyle f bb rv s (style, _) Nothing = do
  style' <- checkStyleRetVal rv style
  -- See if the instructions in the block match the rest of the error
  -- descriptor.  If so, add this function to the error summary with
  -- 'style' as the error reporting method.
  let (unmatchedActions, ws) = foldr checkInstruction (style', []) (basicBlockInstructions bb)
  case S.null unmatchedActions of
    False -> Nothing
    True ->
      let upd = errorSummary %~ HM.insertWith S.union f (S.singleton (style, ws))
      in return $ upd s

-- | Check to see if the returned value is a constant matching the
-- expected return value in the error descriptor.  If it is, remove
-- the return clause from the descriptor and return the rest.
-- Otherwise return Nothing to indicate no match.
checkStyleRetVal :: Value -> Set ErrorAction -> Maybe (Set ErrorAction)
checkStyleRetVal rv desc = do
  act <- F.find isRetAction desc
  case act of
    ReturnConstantInt ivs ->
      case valueContent' rv of
        ConstantC ConstantInt { constantIntValue = (fromIntegral -> irv) } ->
          case irv `S.member` ivs of
            False -> Nothing
            True -> return $ S.delete act desc
        _ -> Nothing
    ReturnConstantPtr pvs ->
      case hasPointerType rv of
        False -> Nothing
        True ->
          case valueContent' rv of
            ConstantC ConstantPointerNull {} ->
              case 0 `S.member` pvs of
                False -> Nothing
                True -> return $ S.delete act desc
            ConstantC ConstantInt { constantIntValue = (fromIntegral -> irv) } ->
              case irv `S.member` pvs of
                False -> Nothing
                True -> return $ S.delete act desc
            _ -> Nothing
    _ -> error "Foreign.Inference.Analysis.ErrorHandling.checkStyleRetVal: Unexpected non-ret action"

hasPointerType :: Value -> Bool
hasPointerType v =
  case valueType v of
    TypePointer _ _ -> True
    _ -> False

isRetAction :: ErrorAction -> Bool
isRetAction (ReturnConstantInt _) = True
isRetAction (ReturnConstantPtr _) = True
isRetAction _ = False

-- | If the given instruction matches any actions in the error
-- descriptor, remove the action from the descriptor.  If the
-- descriptor is empty, we have found error reporting code.
checkInstruction :: Instruction -> (Set ErrorAction, [Witness]) -> (Set ErrorAction, [Witness])
checkInstruction i desc = F.foldl' (removeIfMatchingInst i) desc (fst desc)

removeIfMatchingInst :: Instruction -> (Set ErrorAction, [Witness]) -> ErrorAction -> (Set ErrorAction, [Witness])
removeIfMatchingInst i acc@(desc, ws) act =
  case (i, act) of
    (CallInst { callFunction = (valueContent' -> FunctionC f) }, FunctionCall calleeName _) ->
      let fname = identifierAsString (functionName f)
      in case fname == calleeName of
        False -> acc
        True -> (S.delete act desc, Witness i "matching call inst" : ws)
    _ -> acc

-- 'analyzeErrorChecks' can stay basically the same.  Maybe it changes
-- a bit and doesn't look directly for an ICmpInst in the predicate (it
-- might not be for complex conditionals with && and ||?).
--
-- 'extractErrorHandlingCode' changes.  Instead of pattern matching,
-- it acts as an interpreter and interprets the AST of the condition
-- into a formula that it feeds to Z3.  If the formula construction
-- fails, this is not the type of conditional we can deal with.
--
-- There should be two formulas: one for the true branch and one for the
-- false branch.  The test is: prove $ branch1Facts => hasError
--
-- where hasError is based on the summary we have of the return values
-- of the callee.
--
-- Note, for blocks with multiple predecessors, we just check if *either*
-- tells us that we are handling an error

data CmpOperand = FuncallOperand Value -- the callee (external func or func)
                | ConstIntOperand Int
                | Neither

callFuncOrConst :: Value -> CmpOperand
callFuncOrConst v =
  case valueContent' v of
    ConstantC ConstantInt { constantIntValue = iv } ->
      ConstIntOperand (fromIntegral iv)
    InstructionC CallInst { callFunction = callee } ->
      FuncallOperand callee
    _ -> Neither

extractErrorHandlingCode :: Function -> ErrorSummary
                            -> CmpPredicate -> Value -> Value
                            -> BasicBlock -> BasicBlock
                            -> MaybeT Analysis (Set ErrorAction)
extractErrorHandlingCode f s p v1 v2 tt ft = do
  rel <- cmpPredicateToRelation p
  (trueFormula, falseFormula) <- cmpToFormula s rel v1 v2
  case isTrue trueFormula of
    True -> branchToErrorDescriptor f tt -- `debug` "-->Taking first branch"
    False -> case isTrue falseFormula of
      True -> branchToErrorDescriptor f ft -- `debug` "-->Taking second branch"
      False -> fail "Error not checked"

liftMaybe :: Maybe a -> MaybeT Analysis a
liftMaybe Nothing = fail "liftMaybe"
liftMaybe (Just a) = return a

cmpToFormula :: ErrorSummary
                -> (SInt32 -> SInt32 -> SBool)
                -> Value
                -> Value
                -> MaybeT Analysis (SInt32 -> SBool, SInt32 -> SBool)
cmpToFormula s rel v1 v2 = do
  ics <- lift $ analysisEnvironment indirectCallSummary
  ds <- lift $ analysisEnvironment dependencySummary
  let v1' = callFuncOrConst v1
      v2' = callFuncOrConst v2
  case (v1', v2') of
    (FuncallOperand callee, ConstIntOperand i) -> do
      let callees = callTargets ics callee
      rv <- errorReturnValue ds s callees
      let i' = fromIntegral i
          rv' = fromIntegral rv
          trueFormula = \(x :: SInt32) -> (x .== rv') ==> (x `rel` i')
          falseFormula = \(x :: SInt32) -> (x .== rv') ==> bnot (x `rel` i')
      return (trueFormula, falseFormula)
    (ConstIntOperand i, FuncallOperand callee) -> do
      let callees = callTargets ics callee
      rv <- errorReturnValue ds s callees
      let i' = fromIntegral i
          rv' = fromIntegral rv
          trueFormula = \(x :: SInt32) -> (x .== rv') ==> (i' `rel` x)
          falseFormula = \(x :: SInt32) -> (x .== rv') ==> bnot (i' `rel` x)
      return (trueFormula, falseFormula)
    _ -> fail "cmpToFormula"

cmpPredicateToRelation :: CmpPredicate -> MaybeT Analysis (SInt32 -> SInt32 -> SBool)
cmpPredicateToRelation p =
  case p of
    ICmpEq -> return (.==)
    ICmpNe -> return (./=)
    ICmpUgt -> return (.>)
    ICmpUge -> return (.>=)
    ICmpUlt -> return (.<)
    ICmpUle -> return (.<=)
    ICmpSgt -> return (.>)
    ICmpSge -> return (.>=)
    ICmpSlt -> return (.<)
    ICmpSle -> return (.<=)
    _ -> fail "cmpPredicateToRelation is a floating point comparison"

isTrue :: (SInt32 -> SBool) -> Bool
isTrue = unsafePerformIO . isTheorem
-- isTrue formula = unsafePerformIO $ do
--   putStrLn "Calling z3"
--   res <- isTheorem formula
--   return res

errorReturnValue :: DependencySummary -> ErrorSummary -> [Value] -> MaybeT Analysis Int
errorReturnValue _ _ [] = fail "No call targets"
errorReturnValue ds s [callee] = do
  fsumm <- liftMaybe $ lookupFunctionSummary ds s callee
  liftMaybe $ errRetVal fsumm
errorReturnValue ds s (callee:rest) = do
  fsumm <- liftMaybe $ lookupFunctionSummary ds s callee
  rv <- liftMaybe $ errRetVal fsumm
  mapM_ (checkOtherErrorReturns rv) rest
  return rv
  where
    checkOtherErrorReturns rv c = do
      fsumm <- liftMaybe $ lookupFunctionSummary ds s c
      rv' <- liftMaybe $ errRetVal fsumm
      when (rv' /= rv) $ emitWarning Nothing "ErrorAnalysis" ("Mismatched error return codes for indirect call " ++ show (valueName callee))


errRetVal :: [FuncAnnotation] -> Maybe Int
errRetVal [] = Nothing
errRetVal (FAReportsErrors es : _) = do
  act <- F.find isIntRet es
  case act of
    ReturnConstantInt is ->
      case F.toList is of
        [] -> Nothing
        i:_ -> return i
    ReturnConstantPtr is ->
      case F.toList is of
        [] -> Nothing
        i:_ -> return i
    _ -> Nothing
errRetVal (_:rest) = errRetVal rest

isIntRet :: ErrorAction -> Bool
isIntRet (ReturnConstantInt _) = True
isIntRet (ReturnConstantPtr _) = True
isIntRet _ = False


-- FIXME This needs to get all of the blocks that are in this branch
-- (successors of bb and control dependent on the branch).
branchToErrorDescriptor :: Function -> BasicBlock -> MaybeT Analysis (Set ErrorAction)
branchToErrorDescriptor f bb = do
  brs <- lift $ analysisEnvironment _blockRetLabels
  let rcs = blockReturns brs bb -- `debug` show brs
  constantRcs <- liftMaybe $ mapM retValToConstantInt rcs -- `debug` show rcs
  case null constantRcs {- `debug` show constantRcs -} of
    True -> fail "Non-constant return value"
    False ->
      let rcon = if functionReturnsPointer f then ReturnConstantPtr else ReturnConstantInt
          ract = rcon (S.fromList constantRcs)
          acts = foldr instToAction [ract] (basicBlockInstructions bb)
      in return $ S.fromList acts -- `debug` show constantRcs

retValToConstantInt :: Value -> Maybe Int
retValToConstantInt v =
  case valueContent' v of
    ConstantC ConstantInt { constantIntValue = (fromIntegral -> iv) } ->
      return iv
    _ -> Nothing

functionReturnsPointer :: Function -> Bool
functionReturnsPointer f =
  case functionReturnType f of
    TypePointer _ _ -> True
    _ -> False

instToAction ::Instruction -> [ErrorAction] -> [ErrorAction]
instToAction i acc =
  case i of
    CallInst { callFunction = (valueContent' -> FunctionC f)
             , callArguments = (map fst -> args)
             } ->
      let fname = identifierAsString (functionName f)
          argActs = foldr callArgActions mempty (zip [0..] args)
      in FunctionCall fname argActs : acc
    _ -> acc

callArgActions :: (Int, Value)
                  -> IntMap ErrorActionArgument
                  -> IntMap ErrorActionArgument
callArgActions (ix, v) acc =
  case valueContent' v of
    ArgumentC a ->
      let atype = show (argumentType a)
          aix = argumentIndex a
      in IM.insert ix (ErrorArgument atype aix) acc
    ConstantC ConstantInt { constantIntValue = (fromIntegral -> iv) } ->
      IM.insert ix (ErrorInt iv) acc
    _ -> acc

argumentIndex :: Argument -> Int
argumentIndex a = aix
  where
    f = argumentFunction a
    Just aix = elemIndex a (functionParameters f)
