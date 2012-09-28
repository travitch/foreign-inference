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
import Data.List ( elemIndex )
import Data.Monoid
import Data.SBV
import Data.Set ( Set )
import qualified Data.Set as S
import System.IO.Unsafe ( unsafePerformIO )

import LLVM.Analysis
import LLVM.Analysis.BlockReturnValue
import LLVM.Analysis.CallGraphSCCTraversal
import LLVM.Analysis.CDG
import LLVM.Analysis.Dominance

import Foreign.Inference.AnalysisMonad
import Foreign.Inference.Diagnostics
import Foreign.Inference.Interface
import Foreign.Inference.Analysis.IndirectCallResolver


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

data ErrorData =
  ErrorData { dependencySummary :: DependencySummary
            , indirectCallSummary :: IndirectCallSummary
            , _blockRetLabels :: BlockReturns
            }

$(makeLenses ''ErrorData)

type Analysis = AnalysisMonad ErrorData ()

instance SummarizeModule ErrorSummary where
  summarizeArgument _ _ = []
  summarizeFunction f (ErrorSummary summ _) =
    case HM.lookup f summ of
      Nothing -> []
      Just s ->
        case F.toList s of
          [] -> []
          acts : _ -> [FAReportsErrors acts]

identifyErrorHandling :: forall compositeSummary funcLike . (FuncLike funcLike, HasFunction funcLike, HasCDG funcLike, HasPostdomTree funcLike)
                      => DependencySummary
                      -> IndirectCallSummary
                      -> Simple Lens compositeSummary ErrorSummary
                      -> ComposableAnalysis compositeSummary funcLike
identifyErrorHandling ds ics =
  composableAnalysisM runner errorAnalysis
  where
    runner a = runAnalysis a readOnlyData ()
    readOnlyData = ErrorData ds ics mempty

-- | Find each function call for which we have an error descriptor.
-- Then find the branch handling the error (if there is one) and add
-- that summary to the ErrorSummary for this function.
--
-- Look for br (cmp (call)) patterns
errorAnalysis :: (FuncLike funcLike, HasFunction funcLike, HasCDG funcLike, HasPostdomTree funcLike)
                 => funcLike
                 -> ErrorSummary
                 -> Analysis ErrorSummary
errorAnalysis funcLike s =
  analysisLocal (blockRetLabels .~ retLabels) $
    foldM (analyzeErrorChecks f) s (functionBody f)
  where
    f = getFunction funcLike
    retLabels = labelBlockReturns funcLike

analyzeErrorChecks :: Function
                      -> ErrorSummary
                      -> BasicBlock
                      -> Analysis ErrorSummary
analyzeErrorChecks f s bb =
  case basicBlockTerminatorInstruction bb of
    BranchInst { branchCondition = (valueContent' ->
      InstructionC ICmpInst { cmpPredicate = p
                            , cmpV1 = v1
                            , cmpV2 = v2
                            })
               , branchTrueTarget = tt
               , branchFalseTarget = ft
               } -> do
      mErrDesc <- runMaybeT $ extractErrorHandlingCode s p v1 v2 tt ft
      case mErrDesc of
        Nothing -> return s
        Just errDesc ->
          let upd = errorSummary %~ HM.insertWith S.union f (S.singleton errDesc)
          in return $ upd s
    _ -> return s

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
-- (successors of bb and control dependent on the branch)
branchToErrorDescriptor :: BasicBlock -> MaybeT Analysis ErrorDescriptor
branchToErrorDescriptor bb = do
  brs <- lift $ analysisEnvironment _blockRetLabels
  rc <- liftMaybe $ blockReturn brs bb
  case valueContent' rc of
    ConstantC ConstantInt { constantIntValue = iv } ->
      let ract = ReturnConstantInt (S.singleton (fromIntegral iv))
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
          argActs = foldr callArgActions [] (zip [0..] args)
      in FunctionCall fname argActs : acc
    _ -> acc

callArgActions :: (Int, Value)
                  -> [(Int, ErrorActionArgument)]
                  -> [(Int, ErrorActionArgument)]
callArgActions (ix, v) acc =
  case valueContent' v of
    ArgumentC a ->
      let atype = show (argumentType a)
          aix = argumentIndex a
      in (ix, ErrorArgument atype aix) : acc
    ConstantC ConstantInt { constantIntValue = (fromIntegral -> iv) } ->
      (ix, ErrorInt iv) : acc
    _ -> acc

argumentIndex :: Argument -> Int
argumentIndex a = aix
  where
    f = argumentFunction a
    Just aix = elemIndex a (functionParameters f)
