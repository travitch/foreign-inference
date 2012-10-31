{-# LANGUAGE ViewPatterns, RankNTypes, ScopedTypeVariables #-}
{-# LANGUAGE DeriveGeneric, TemplateHaskell #-}
-- | This analysis attempts to automatically identify error-handling
-- code in libraries.
--
-- The error laws are:
--
--  * (Transitive error) If function F returns the result of calling
--    callee C directly, and C has error handling pattern P, then F
--    has error handling pattern P.
--
--  * (Known error) If function F checks the result of calling C for
--    an error condition and performs some action ending in a constant
--    integer error return code, that is error handling code.  Actions
--    are assigning to globals and calling functions. (Note: may need
--    to make this a non-zero return).
--
--  * (Generalize return) If F calls any (all?) of the functions in an
--    error descriptor and then returns a constant int I, I is a new
--    error code used in this library.
--
--  * (Generalize action) If a function F returns a constant int I
--    that is the return code for a known error handling pattern, then
--    the functions called on that branch are a new error handling
--    pattern.
module Foreign.Inference.Analysis.ErrorHandling (
  ErrorSummary,
  identifyErrorHandling,
  -- * Testing
  -- allocatorSummaryToTestFormat
  ) where

import GHC.Generics

import Control.DeepSeq
import Control.DeepSeq.Generics ( genericRnf )
import Control.Monad ( foldM, when )
import Control.Monad.Trans.Class
import Control.Monad.Trans.Maybe
import qualified Data.Foldable as F
import Data.HashMap.Strict ( HashMap )
import qualified Data.HashMap.Strict as HM
import Data.IntMap ( IntMap )
import qualified Data.IntMap as IM
import Data.List ( elemIndex )
import Data.List.NonEmpty ( NonEmpty(..) )
import qualified Data.List.NonEmpty as NEL
import Data.Maybe ( fromMaybe )
import Data.Monoid
import Data.SBV
import Data.Set ( Set )
import qualified Data.Set as S
import System.IO.Unsafe ( unsafePerformIO )

import LLVM.Analysis
import LLVM.Analysis.BlockReturnValue

import Foreign.Inference.AnalysisMonad
import Foreign.Inference.Diagnostics
import Foreign.Inference.Interface
import Foreign.Inference.Internal.FlattenValue
import Foreign.Inference.Analysis.IndirectCallResolver

-- import Text.Printf
-- import Debug.Trace
-- debug :: a -> String -> a
-- debug = flip trace

-- | An ErrorDescriptor describes a site in the program handling an
-- error (along with a witness).
data ErrorDescriptor =
  ErrorDescriptor { errorActions :: Set ErrorAction
                  , errorReturns :: ErrorReturn
                  , errorWitnesses :: [Witness]
                  }
  deriving (Eq, Ord, Generic, Show)

instance NFData ErrorDescriptor where
  rnf = genericRnf

-- | The error summary is the type exposed to callers, mapping each
-- function to its error handling methods.
type SummaryType = HashMap Function (Set ErrorDescriptor)
data ErrorSummary =
  ErrorSummary { errorSummary :: SummaryType
               , errorDiagnostics :: Diagnostics
               }
  deriving (Generic)

instance Eq ErrorSummary where
  (ErrorSummary s1 _) == (ErrorSummary s2 _) = s1 == s2

instance Monoid ErrorSummary where
  mempty = ErrorSummary mempty mempty
  mappend (ErrorSummary m1 d1) (ErrorSummary m2 d2) =
    ErrorSummary (HM.union m1 m2) (mappend d1 d2)

instance NFData ErrorSummary where
  rnf = genericRnf

-- This is a manual lens implementation as described in the lens
-- package.
instance HasDiagnostics ErrorSummary where
  diagnosticLens f (ErrorSummary s d) =
    fmap (\d' -> ErrorSummary s d') (f d)

data ErrorData =
  ErrorData { dependencySummary :: DependencySummary
            , indirectCallSummary :: IndirectCallSummary
            }

-- | This is the data we want to bootstrap through the two
-- generalization rules
data ErrorState =
  ErrorState { errorCodes :: Set Int
             , errorFunctions :: Set String
             }

instance Monoid ErrorState where
  mempty = ErrorState mempty mempty
  mappend (ErrorState c1 f1) (ErrorState c2 f2) =
    ErrorState (c1 `mappend` c2) (f1 `mappend` f2)


type Analysis = AnalysisMonad ErrorData ErrorState

identifyErrorHandling :: (HasFunction funcLike, HasBlockReturns funcLike)
                         => [funcLike]
                         -> DependencySummary
                         -> IndirectCallSummary
                         -> ErrorSummary
identifyErrorHandling funcLikes ds ics =
  runAnalysis analysis roData mempty
  where
    roData = ErrorData ds ics
    analysis = do
      res <- fixAnalysis mempty
      -- The diagnostics will be filled in automatically by runAnalysis
      return $ ErrorSummary res mempty
    fixAnalysis res = do
      res' <- foldM errorAnalysis res funcLikes
      if res == res' then return res
        else fixAnalysis res'

-- | FIXME If the error handling patterns of a function can't be
-- unified simply, just include the return codes here.
--
-- Always combine return values
instance SummarizeModule ErrorSummary where
  summarizeArgument _ _ = []
  summarizeFunction f (ErrorSummary summ _) = fromMaybe [] $ do
    fsumm <- HM.lookup f summ
    descs <- NEL.nonEmpty (F.toList fsumm)
    let retcodes = unifyReturnCodes descs
        ws = concatMap errorWitnesses (NEL.toList descs)
    case unifyErrorActions descs of
      Nothing -> return [(FAReportsErrors mempty retcodes, ws)]
      Just uacts -> return [(FAReportsErrors uacts retcodes, ws)]

-- | FIXME: Prefer error actions of size one (should discard extraneous
-- actions like cleanup code).
unifyErrorActions :: NonEmpty ErrorDescriptor -> Maybe (Set ErrorAction)
unifyErrorActions d0 = foldr unifyActions (Just d) ds
  where
    (d:|ds) = fmap errorActions d0
    unifyActions _ Nothing = Nothing
    unifyActions s1 acc@(Just s2)
      | S.size s1 == 1 && S.size s2 /= 1 = Just s1
      | s1 == s2 = acc
      | otherwise = Nothing

-- | Merge all return values; if ints and ptrs are mixed, prefer the
-- ints
unifyReturnCodes :: NonEmpty ErrorDescriptor -> ErrorReturn
unifyReturnCodes = F.foldr1 unifyReturns . fmap errorReturns
  where
    unifyReturns (ReturnConstantInt is1) (ReturnConstantInt is2) =
      ReturnConstantInt (is1 `S.union` is2)
    unifyReturns (ReturnConstantPtr is1) (ReturnConstantPtr is2) =
      ReturnConstantPtr (is1 `S.union` is2)
    unifyReturns (ReturnConstantPtr _) r@(ReturnConstantInt _) = r
    unifyReturns r@(ReturnConstantInt _) (ReturnConstantPtr _) = r


errorAnalysis :: (HasFunction funcLike, HasBlockReturns funcLike)
                 => SummaryType -> funcLike -> Analysis SummaryType
errorAnalysis summ funcLike = do
  summ' <- returnsTransitiveError f summ
  foldM (errorsForBlock f retLabels) summ' (functionBody f)
  where
    f = getFunction funcLike
    retLabels = getBlockReturns funcLike

-- | Find the error handling code in this block
errorsForBlock :: Function
                  -> BlockReturns
                  -> SummaryType
                  -> BasicBlock
                  -> Analysis SummaryType
errorsForBlock f brets s bb = do
  takeFirst s [ handlesKnownError f brets s bb
              , matchActionAndGeneralizeReturn f brets s bb
              ]
  where
    takeFirst :: (Monad m) => a -> [m (Maybe a)] -> m a
    takeFirst def [] = return def
    takeFirst def (act:rest) = do
      res <- act
      maybe (takeFirst def rest) return res

-- | If the function transitively returns errors, record them
-- in the error summary
returnsTransitiveError :: Function -> SummaryType -> Analysis SummaryType
returnsTransitiveError f summ = do
  ds <- analysisEnvironment dependencySummary
  ics <- analysisEnvironment indirectCallSummary
  return $ fromMaybe summ $ do
    exitInst <- functionExitInstruction f
    case exitInst of
      RetInst { retInstValue = Just rv } ->
        let rvs = flattenValue rv
        in return $ foldr (checkTransitiveError ics ds) summ rvs
      _ -> return summ
  where
    checkTransitiveError :: IndirectCallSummary
                            -> DependencySummary
                            -> Value
                            -> SummaryType
                            -> SummaryType
    checkTransitiveError ics ds rv s =
      case valueContent' rv of
        InstructionC i@CallInst { callFunction = callee } ->
          let callees = callTargets ics callee
          in foldr (recordTransitiveError ds i) s callees
        _ -> s

    recordTransitiveError :: DependencySummary -> Instruction
                             -> Value -> SummaryType
                             -> SummaryType
    recordTransitiveError ds i callee s = fromMaybe s $ do
      fsumm <- lookupFunctionSummary ds (ErrorSummary s mempty) callee
      FAReportsErrors errActs eret <- F.find isErrRetAnnot fsumm
      let w = Witness i "transitive error"
          d = ErrorDescriptor errActs eret [w]
      return $ HM.insertWith S.union f (S.singleton d) s

-- | If the function handles an error from a callee that we already
-- know about, this will tell us what this caller does in response.
handlesKnownError :: Function
                     -> BlockReturns
                     -> SummaryType
                     -> BasicBlock
                     -> Analysis (Maybe SummaryType)
handlesKnownError f brets s bb =
  case basicBlockTerminatorInstruction bb of
    bi@BranchInst { branchCondition = (valueContent' ->
      InstructionC ci@ICmpInst { cmpPredicate = p
                               , cmpV1 = v1
                               , cmpV2 = v2
                               })
               , branchTrueTarget = tt
               , branchFalseTarget = ft
               } -> runMaybeT $ do
      errDesc <- extractErrorHandlingCode f brets s p v1 v2 tt ft
      let acts = errorActions errDesc
      when (S.size acts == 1) $ do
        st <- analysisGet
        case F.find isFuncallAct acts of
          Just (FunctionCall fname _) ->
            analysisPut st { errorFunctions = S.insert fname (errorFunctions st) }
          _ -> return ()
      let w1 = Witness ci "check error return"
          w2 = Witness bi "return error code"
          d = errDesc { errorWitnesses = [w1, w2] }
      return $! HM.insertWith S.union f (S.singleton d) s
    _ -> return Nothing

isFuncallAct :: ErrorAction -> Bool
isFuncallAct a =
  case a of
    FunctionCall _ _ -> True
    _ -> False

-- | Try to generalize (learn new error codes) based on called error
-- functions
matchActionAndGeneralizeReturn :: Function
                                  -> BlockReturns
                                  -> SummaryType
                                  -> BasicBlock
                                  -> Analysis (Maybe SummaryType)
matchActionAndGeneralizeReturn f brets s bb =
  -- If this basic block calls any functions in the errFuncs set, then
  -- use branchToErrorDescriptor f bb to compute a new error
  -- descriptor and then add the return value to the errCodes set.
  runMaybeT $ do
    edesc <- branchToErrorDescriptor f brets bb
    st <- lift $ analysisGet
    let fs = errorFunctions st
    FunctionCall ecall _ <- liftMaybe $ F.find (isErrorFuncCall fs) (errorActions edesc)
    case errorReturns edesc of
      ReturnConstantPtr _ -> fail "Ptr return"
      ReturnConstantInt is -> do
        let ti = basicBlockTerminatorInstruction bb
            w = Witness ti ("Called " ++ ecall)
            d = edesc { errorWitnesses = [w] }
        lift $ analysisPut st { errorCodes = errorCodes st `S.union` is }
        return $! HM.insertWith S.union f (S.singleton d) s

isErrorFuncCall :: Set String -> ErrorAction -> Bool
isErrorFuncCall funcSet errAct =
  case errAct of
    FunctionCall s _ -> S.member s funcSet
    _ -> False

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

extractErrorHandlingCode :: Function -> BlockReturns -> SummaryType
                            -> CmpPredicate -> Value -> Value
                            -> BasicBlock -> BasicBlock
                            -> MaybeT Analysis ErrorDescriptor
extractErrorHandlingCode f brets s p v1 v2 tt ft = do
  rel <- cmpPredicateToRelation p
  (trueFormula, falseFormula) <- cmpToFormula s rel v1 v2
  case isTrue trueFormula of
    True -> branchToErrorDescriptor f brets tt -- `debug` "-->Taking first branch"
    False -> case isTrue falseFormula of
      True -> branchToErrorDescriptor f brets ft -- `debug` "-->Taking second branch"
      False -> fail "Error not checked"

liftMaybe :: Maybe a -> MaybeT Analysis a
liftMaybe Nothing = fail "liftMaybe"
liftMaybe (Just a) = return a

cmpToFormula :: SummaryType
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

errorReturnValue :: DependencySummary -> SummaryType -> [Value] -> MaybeT Analysis Int
errorReturnValue _ _ [] = fail "No call targets"
errorReturnValue ds s [callee] = do
  fsumm <- liftMaybe $ lookupFunctionSummary ds (ErrorSummary s mempty) callee
  liftMaybe $ errRetVal fsumm
errorReturnValue ds s (callee:rest) = do
  fsumm <- liftMaybe $ lookupFunctionSummary ds (ErrorSummary s mempty) callee
  rv <- liftMaybe $ errRetVal fsumm
  mapM_ (checkOtherErrorReturns rv) rest
  return rv
  where
    checkOtherErrorReturns rv c = do
      fsumm <- liftMaybe $ lookupFunctionSummary ds (ErrorSummary s mempty) c
      rv' <- liftMaybe $ errRetVal fsumm
      when (rv' /= rv) $ emitWarning Nothing "ErrorAnalysis" ("Mismatched error return codes for indirect call " ++ show (valueName callee))


errRetVal :: [FuncAnnotation] -> Maybe Int
errRetVal [] = Nothing
errRetVal (FAReportsErrors _ ract : _) = do
--  act <- F.find isIntRet es
  case ract of
    ReturnConstantInt is ->
      case F.toList is of
        [] -> Nothing
        i:_ -> return i
    ReturnConstantPtr is ->
      case F.toList is of
        [] -> Nothing
        i:_ -> return i
errRetVal (_:rest) = errRetVal rest


callTargets :: IndirectCallSummary -> Value -> [Value]
callTargets ics callee =
  case valueContent' callee of
    FunctionC _ -> [callee]
    ExternalFunctionC _ -> [callee]
    _ -> indirectCallInitializers ics callee

isErrRetAnnot :: FuncAnnotation -> Bool
isErrRetAnnot (FAReportsErrors _ _) = True
isErrRetAnnot _ = False

-- FIXME This needs to get all of the blocks that are in this branch
-- (successors of bb and control dependent on the branch).
branchToErrorDescriptor :: Function -> BlockReturns -> BasicBlock
                           -> MaybeT Analysis ErrorDescriptor
branchToErrorDescriptor f brs bb = do
  let rcs = blockReturns brs bb -- `debug` show brs
  constantRcs <- liftMaybe $ mapM retValToConstantInt rcs -- `debug` show rcs
  case null constantRcs {- `debug` show constantRcs -} of
    True -> fail "Non-constant return value"
    False ->
      let rcon = if functionReturnsPointer f
                 then ReturnConstantPtr
                 else ReturnConstantInt
          ract = rcon (S.fromList constantRcs)
          acts = foldr instToAction [] (basicBlockInstructions bb)
      in return $! ErrorDescriptor (S.fromList acts) ract [] -- `debug` show constantRcs

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
