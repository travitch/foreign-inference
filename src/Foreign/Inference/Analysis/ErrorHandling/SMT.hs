{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
module Foreign.Inference.Analysis.ErrorHandling.SMT (
  computeInducedFacts,
  isSat,
  ignoreCasts
  ) where

import Control.Monad.State.Strict
import Data.HashMap.Strict ( HashMap )
import qualified Data.HashMap.Strict as HM
import Data.Maybe ( catMaybes )
import Data.SBV
import Data.Set ( Set )
import qualified Data.Set as S
import System.IO.Unsafe ( unsafePerformIO )

import LLVM.Analysis
import LLVM.Analysis.BlockReturnValue
import LLVM.Analysis.CDG
import LLVM.Analysis.CFG
import LLVM.Analysis.Dominance

type FormulaBuilder = State (Set Instruction, HashMap (BasicBlock, Instruction) (Maybe (SInt32 -> SBool)))

computeInducedFacts :: (HasFunction funcLike, HasBlockReturns funcLike,
                        HasCFG funcLike, HasCDG funcLike, HasDomTree funcLike)
                    => funcLike
                    -> BasicBlock
                    -> Instruction
                    -> FormulaBuilder (Maybe (SInt32 -> SBool))
computeInducedFacts funcLike bb0 target
  | S.null cdeps = return Nothing
  | otherwise = buildRelevantFacts bb0
  where
    ti0 = basicBlockTerminatorInstruction bb0
    cdeps = S.fromList $ controlDependencies funcLike ti0
    buildRelevantFacts bb
      | otherwise =
        let ti = basicBlockTerminatorInstruction bb
            dirCdeps = directControlDependencies funcLike ti
        in case dirCdeps of
          [] -> return Nothing
          [singleDep] -> memoBuilder bb singleDep
          _ -> do
            fs <- mapM (memoBuilder bb) dirCdeps
            case catMaybes fs of
              [] -> return Nothing
              fs' -> return $ Just $ \(x :: SInt32) -> bAny ($ x) fs'

    memoBuilder :: BasicBlock -> Instruction
                -> FormulaBuilder (Maybe (SInt32 -> SBool))
    memoBuilder bb cdep = do
      (visited, s) <- get
      case HM.lookup (bb, cdep) s of
        Just f -> return f
        Nothing ->
          case S.member cdep visited of
            True -> return Nothing
            False -> do
              put (S.insert cdep visited, s)
              factBuilder bb cdep
    factBuilder :: BasicBlock -> Instruction
                -> FormulaBuilder (Maybe (SInt32 -> SBool))
    factBuilder bb cdep = do
      let Just cdepBlock = instructionBasicBlock cdep
      case cdep of
        BranchInst { branchTrueTarget = tt
                   , branchCondition = (valueContent' ->
          InstructionC ICmpInst { cmpPredicate = p
                                , cmpV1 = val1
                                , cmpV2 = val2
                                })}
            | ignoreCasts val1 == toValue target ||
              ignoreCasts val2 == toValue target -> do
                let doNeg = if blockDominates funcLike tt bb then id else bnot
                    thisFact = inducedFact val1 val2 p doNeg
                innerFact <- buildRelevantFacts cdepBlock
                let fact' = liftedConjoin thisFact innerFact
                (vis, st) <- get
                put $ (vis, HM.insert (bb, cdep) fact' st)
                return fact'
            | otherwise -> buildRelevantFacts cdepBlock
        _ -> return Nothing


liftedConjoin :: Maybe (SInt32 -> SBool) -> Maybe (SInt32 -> SBool)
              -> Maybe (SInt32 -> SBool)
liftedConjoin Nothing Nothing = Nothing
liftedConjoin f1@(Just _) Nothing = f1
liftedConjoin Nothing f2@(Just _) = f2
liftedConjoin (Just f1) (Just f2) = Just $ \(x :: SInt32) -> f1 x &&& f2 x

blockDominates :: (HasDomTree t) => t -> BasicBlock -> BasicBlock -> Bool
blockDominates f b1 b2 = dominates f i1 i2
  where
    i1 = basicBlockTerminatorInstruction b1
    i2 = basicBlockTerminatorInstruction b2

-- | Given a formula that holds up to the current location @mf@, augment
-- it by conjoining the new fact we are introducing (if any).  The new
-- fact is derived from the relationship ('CmpPredicate') between the two
-- 'Value' arguments.
inducedFact :: Value -> Value -> CmpPredicate
            -> (SBool -> SBool) -> Maybe (SInt32 -> SBool)
inducedFact val1 val2 p doNeg = do
  rel <- cmpPredicateToRelation p
  case (valueContent' val1, valueContent' val2) of
    (ConstantC ConstantInt { constantIntValue = (fromIntegral -> iv) }, _) ->
      return $ \(x :: SInt32) -> doNeg (iv `rel` x)
    (_, ConstantC ConstantInt { constantIntValue = (fromIntegral -> iv)}) ->
      return $ \(x :: SInt32) -> doNeg (x `rel` iv)
    (ConstantC ConstantPointerNull {}, _) ->
      return $ \(x :: SInt32) -> doNeg (0 `rel` x)
    (_, ConstantC ConstantPointerNull {}) ->
      return $ \(x :: SInt32) -> doNeg (x `rel` 0)
    -- Not a comparison against a constant int, so we didn't learn anything.
    -- This is different from failure - we still had whatever information we
    -- had from before.
    _ -> fail "Cannot produce a fact here"

cmpPredicateToRelation :: CmpPredicate -> Maybe (SInt32 -> SInt32 -> SBool)
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

isSat :: (SInt32 -> SBool) -> Bool
isSat f = unsafePerformIO $ do
  Just sr <- isSatisfiable Nothing f
  return sr

ignoreCasts :: Value -> Value
ignoreCasts v =
  case valueContent v of
    InstructionC BitcastInst { castedValue = cv } -> ignoreCasts cv
    InstructionC TruncInst { castedValue = cv } -> ignoreCasts cv
    InstructionC ZExtInst { castedValue = cv } -> ignoreCasts cv
    InstructionC SExtInst { castedValue = cv } -> ignoreCasts cv
    InstructionC IntToPtrInst { castedValue = cv } -> ignoreCasts cv
    GlobalAliasC GlobalAlias { globalAliasTarget = t } -> ignoreCasts t
    ConstantC ConstantValue { constantInstruction = BitcastInst { castedValue = cv } } -> ignoreCasts cv
    _ -> valueContent v


