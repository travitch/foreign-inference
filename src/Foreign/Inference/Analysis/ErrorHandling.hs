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
import Control.Monad ( foldM )
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

-- import Text.Printf
import Debug.Trace
debug :: a -> String -> a
debug = flip trace

type ErrorDescriptor = Set ErrorAction
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
  case NEL.nonEmpty (HM.elems s) of
    Nothing -> []
    Just hdlrs ->
      let funcErrorHandlers = fmap unifyErrorHandler hdlrs
      in [F.foldr1 combineHandler funcErrorHandlers]

-- | Note, this uses foldr1 but each set cannot be empty (since we use
-- insertWith below, we can't have empty sets).
unifyErrorHandler :: Set ErrorDescriptor -> ErrorDescriptor
unifyErrorHandler = F.foldr1 combineHandler

-- | For each action in the first set, find a corresponding action in
-- the second set.  If there is a match, find the common part they
-- share and insert it into the result.  Otherwise, discard it.
combineHandler :: ErrorDescriptor -> ErrorDescriptor -> ErrorDescriptor
combineHandler d0 = snd . F.foldr findCorresponding (d0, mempty)
  where
    findCorresponding act (targets, acc) =
      case F.foldr (unifyErrorAction act) Nothing targets of
        Nothing -> (targets, acc)
        Just (act', t) ->
          (S.delete t targets, S.insert act' acc)

unifyErrorAction :: ErrorAction
                    -> ErrorAction
                    -> Maybe (ErrorAction, ErrorAction)
                    -> Maybe (ErrorAction, ErrorAction)
unifyErrorAction _ _ j@(Just _) = j
unifyErrorAction a1 a2 Nothing =
  case (a1, a2) of
    (ReturnConstantInt s1, ReturnConstantInt s2) ->
      return (ReturnConstantInt (s1 `S.union` s2), a2)
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
          Just acts ->
            [FAReportsErrors (F.foldr1 combineHandler acts)]

identifyErrorHandling :: forall compositeSummary funcLike . (FuncLike funcLike, HasFunction funcLike, HasCDG funcLike, HasPostdomTree funcLike, HasCFG funcLike)
                         => Module
                         -> DependencySummary
                         -> Simple Lens compositeSummary ErrorSummary
                         -> ComposableAnalysis compositeSummary funcLike
identifyErrorHandling m ds =
  composableAnalysisM runner errorAnalysis
  where
    runner a = runAnalysis a readOnlyData ()
    readOnlyData = ErrorData ds mempty (distillSummary seed)

    funcLikes :: [funcLike]
    funcLikes = map fromFunction (moduleDefinedFunctions m)
    analysis0 = foldM (flip errorAnalysis) mempty funcLikes
    readOnly0 = ErrorData ds mempty mempty
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
    foldM (analyzeErrorChecks f) s (functionBody f)
  where
    f = getFunction funcLike
    retLabels = labelBlockReturns funcLike

-- FIXME: If the first check fails (for a lower-level library error
-- handled), check to see if the block matches any of the error
-- descriptors we have seen so far
--
-- lift $ analysisEnvironment errorSeed
--
-- If the block has a guaranteed return value and the error pattern
-- has a RetConstantInt clause, use that as a filtering check (then
-- remove the return from the pattern because it isn't in the same
-- basic block).
analyzeErrorChecks :: Function
                      -> ErrorSummary
                      -> BasicBlock
                      -> Analysis ErrorSummary
analyzeErrorChecks f s bb = do
  takeFirst s [ handlesKnownError f s bb
              , executesLearnedErrorPattern f s bb
              ]

takeFirst :: (Monad m) => a -> [m (Maybe a)] -> m a
takeFirst def [] = return def
takeFirst def (act:rest) = do
  res <- act
  maybe (takeFirst def rest) return res

handlesKnownError :: Function
                     -> ErrorSummary
                     -> BasicBlock
                     -> Analysis (Maybe ErrorSummary)
handlesKnownError f s bb =
  case basicBlockTerminatorInstruction bb of
    BranchInst { branchCondition = (valueContent' ->
      InstructionC ICmpInst { cmpPredicate = p
                            , cmpV1 = v1
                            , cmpV2 = v2
                            })
               , branchTrueTarget = tt
               , branchFalseTarget = ft
               } -> runMaybeT $ do
      errDesc <- extractErrorHandlingCode s p v1 v2 tt ft
      let upd = errorSummary %~ HM.insertWith S.union f (S.singleton errDesc)
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
checkLearnedStyle f bb rv s style Nothing = do
  style' <- checkStyleRetVal rv style
  -- See if the instructions in the block match the rest of the error
  -- descriptor.  If so, add this function to the error summary with
  -- 'style' as the error reporting method.
  let unmatchedActions = foldr checkInstruction style' (basicBlockInstructions bb)
  case S.null unmatchedActions of
    False -> Nothing
    True ->
      let upd = errorSummary %~ HM.insertWith S.union f (S.singleton style)
      in return $ upd s

-- | Check to see if the returned value is a constant matching the
-- expected return value in the error descriptor.  If it is, remove
-- the return clause from the descriptor and return the rest.
-- Otherwise return Nothing to indicate no match.
checkStyleRetVal :: Value -> ErrorDescriptor -> Maybe ErrorDescriptor
checkStyleRetVal rv desc = do
  act@(ReturnConstantInt ivs) <- F.find isRetAction desc
  case valueContent' rv of
    ConstantC ConstantInt { constantIntValue = (fromIntegral -> irv) } ->
      case irv `S.member` ivs of
        False -> Nothing
        True -> return $ S.delete act desc
    _ -> Nothing

isRetAction :: ErrorAction -> Bool
isRetAction (ReturnConstantInt _) = True
isRetAction _ = False

-- | If the given instruction matches any actions in the error
-- descriptor, remove the action from the descriptor.  If the
-- descriptor is empty, we have found error reporting code.
checkInstruction :: Instruction -> ErrorDescriptor -> ErrorDescriptor
checkInstruction i desc = F.foldl' (removeIfMatchingInst i) desc desc

removeIfMatchingInst :: Instruction -> ErrorDescriptor -> ErrorAction -> ErrorDescriptor
removeIfMatchingInst i desc act =
  case (i, act) of
    (CallInst { callFunction = (valueContent' -> FunctionC f) }, FunctionCall calleeName _) ->
      let fname = identifierAsString (functionName f)
      in case fname == calleeName of
        False -> desc
        True -> S.delete act desc
    _ -> desc

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

extractErrorHandlingCode :: ErrorSummary
                            -> CmpPredicate -> Value -> Value
                            -> BasicBlock -> BasicBlock
                            -> MaybeT Analysis ErrorDescriptor
extractErrorHandlingCode s p v1 v2 tt ft = do
  rel <- cmpPredicateToRelation p
  (trueFormula, falseFormula) <- cmpToFormula s rel v1 v2
  case isTrue trueFormula of
    True -> branchToErrorDescriptor tt
    False -> case isTrue falseFormula of
      True -> branchToErrorDescriptor ft
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
  ds <- lift $ analysisEnvironment dependencySummary
  let v1' = callFuncOrConst v1
      v2' = callFuncOrConst v2
  case (v1', v2') of
    (FuncallOperand callee, ConstIntOperand i) -> do
      fsumm <- liftMaybe $ lookupFunctionSummary ds s callee
      rv <- liftMaybe $ errRetVal fsumm
      let i' = fromIntegral i
          rv' = fromIntegral rv
          trueFormula = \(x :: SInt32) -> (x .== rv') ==> (x `rel` i')
          falseFormula = \(x :: SInt32) -> (x .== rv') ==> bnot (x `rel` i')
      return (trueFormula, falseFormula)
    (ConstIntOperand i, FuncallOperand callee) -> do
      fsumm <- liftMaybe $ lookupFunctionSummary ds s callee
      rv <- liftMaybe $ errRetVal fsumm
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

errRetVal :: [FuncAnnotation] -> Maybe Int
errRetVal [] = Nothing
errRetVal (FAReportsErrors es : _) = do
  ReturnConstantInt is <- F.find isIntRet es
  case F.toList is of
    [] -> Nothing
    (i:_) -> return i
errRetVal (_:rest) = errRetVal rest

isIntRet :: ErrorAction -> Bool
isIntRet (ReturnConstantInt _) = True
isIntRet _ = False


-- FIXME This needs to get all of the blocks that are in this branch
-- (successors of bb and control dependent on the branch).
branchToErrorDescriptor :: BasicBlock -> MaybeT Analysis ErrorDescriptor
branchToErrorDescriptor bb = do
  brs <- lift $ analysisEnvironment _blockRetLabels
  rc <- liftMaybe $ blockReturn brs bb
  case valueContent' rc of
    ConstantC ConstantInt { constantIntValue = (fromIntegral -> iv) } ->
      let ract = ReturnConstantInt (S.singleton iv)
          acts = foldr instToAction [] (basicBlockInstructions bb)
      in return $ S.fromList (ract : acts)
    _ -> fail "Non-constant return value"

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
