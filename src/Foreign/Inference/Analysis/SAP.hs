{-# LANGUAGE TemplateHaskell, DeriveGeneric, ViewPatterns #-}
{-# LANGUAGE RankNTypes #-}
-- | An analysis to identify @Symbolic Access Paths@ for each function
-- in a Module.
module Foreign.Inference.Analysis.SAP (
  SAPSummary,
  identifySAPs
  ) where

import GHC.Generics ( Generic )

import Control.DeepSeq
import Control.DeepSeq.Generics ( genericRnf )
import Control.Lens ( Simple, makeLenses, (%~), (.~) )
import Control.Monad ( foldM )
import Data.Map ( Map )
import qualified Data.Map as M
import Data.Maybe ( fromMaybe, mapMaybe )
import Data.Monoid
import Data.Set ( Set )
import qualified Data.Set as S

import LLVM.Analysis
import LLVM.Analysis.AccessPath
import LLVM.Analysis.CallGraphSCCTraversal

import Foreign.Inference.AnalysisMonad
import Foreign.Inference.Diagnostics
import Foreign.Inference.Interface

data AugmentedAccessPath = WritePath !Int AbstractAccessPath !Int
                         deriving (Eq, Ord, Show, Generic)

instance NFData AugmentedAccessPath where
  rnf = genericRnf

type ReturnPath = (Int, AbstractAccessPath)

data SAPSummary =
  SAPSummary { _sapReturns :: Map Function (Set ReturnPath)
             , _sapArguments :: Map Function (Set AugmentedAccessPath)
             , _sapDiagnostics :: Diagnostics
             }
  deriving (Generic)

$(makeLenses ''SAPSummary)

instance Eq SAPSummary where
  (SAPSummary r1 a1 _) == (SAPSummary r2 a2 _) =
    r1 == r2 && a1 == a2

instance Monoid SAPSummary where
  mempty = SAPSummary mempty mempty mempty
  mappend (SAPSummary r1 a1 d1) (SAPSummary r2 a2 d2) =
    SAPSummary (M.union r1 r2) (M.unionWith S.union a1 a2) (d1 `mappend` d2)

instance NFData SAPSummary where
  rnf = genericRnf

instance HasDiagnostics SAPSummary where
  diagnosticLens = sapDiagnostics

type Analysis = AnalysisMonad () ()

instance SummarizeModule SAPSummary where
  summarizeArgument _ _ = []
  summarizeFunction _ _ = []

identifySAPs :: (FuncLike funcLike, HasFunction funcLike)
                => DependencySummary
                -> Simple Lens compositeSummary SAPSummary
                -> ComposableAnalysis compositeSummary funcLike
identifySAPs ds lns =
  composableAnalysisM runner sapAnalysis lns
  where
    runner a = runAnalysis a ds () ()

{-
data AugmentedAccessPath = ReturnPath !Int AbstractAccessPath
                         | WritePath !Int AbstractAccessPath !Int
                         deriving (Eq, Ord, Show, Generic)
-}

-- | For non-void functions, first check the return instruction and
-- see if it is returning some access path.  Next, just iterate over
-- all stores.
--
-- At call intructions, extend callee paths that are passed some path
-- based on an argument.
sapAnalysis :: (FuncLike funcLike, HasFunction funcLike)
               => funcLike
               -> SAPSummary
               -> Analysis SAPSummary
sapAnalysis flike s =
  foldM (sapTransfer f) s (functionInstructions f)
  where
    f = getFunction flike

sapTransfer :: Function
               -> SAPSummary
               -> Instruction
               -> Analysis SAPSummary
sapTransfer f s i =
  case i of
    RetInst { retInstValue = Just (valueContent' ->
      InstructionC PhiNode { phiIncomingValues = (map fst -> ivs) })} ->
      foldM (returnValueTransfer f) s (valuesAsInsts ivs)
    RetInst { retInstValue = Just (valueContent' ->
      InstructionC SelectInst { selectTrueValue = tv, selectFalseValue = fv })} ->
      foldM (returnValueTransfer f) s (valuesAsInsts [tv, fv])
    RetInst { retInstValue = Just (valueContent' -> InstructionC ri) } ->
      returnValueTransfer f s ri

-- | When the result of a call is returned, that call is known to
-- return an access path *into* one of its arguments.  What we need to
-- do here is figure out which of the callee's arguments the access
-- path uses (the Int the AAP is tagged with).
--
-- We then take the actual argument at that index and look up its
-- access path.  If that concrete access path is rooted at an
-- argument, we get the index of that argument and then append the
-- access paths.
transitiveReturnTransfer :: Function
                            -> SAPSummary
                            -> Function
                            -> [Value]
                            -> Analysis SAPSummary
transitiveReturnTransfer f s@(SAPSummary rs _ _) callee args =
  case M.lookup callee rs of
    Nothing -> return s
    Just rpaths -> do
      let trpaths = mapMaybe extendRPath $ S.toList rpaths
          rs' = foldr (M.insertWith S.union f) rs trpaths
      return $ (sapReturns .~ rs') s
  where
    extendRPath (ix, p) = do
      actual <- safeIndex ix args
      i <- toInstruction actual
      cap <- accessPath i
      formal <- accessPathBaseArgument cap
      let absPath = abstractAccessPath cap
          tix = argumentIndex formal
      tp <- absPath `appendAccessPath` p
      return $ S.singleton (tix, tp)

-- type ReturnPath = (Int, AbstractAccessPath)

-- FIXME: This could actually probably work on external functions,
-- too, if we are careful in representing access paths
returnValueTransfer :: Function
                       -> SAPSummary
                       -> Instruction
                       -> Analysis SAPSummary
returnValueTransfer f s CallInst { callArguments = (map fst -> args)
                                      , callFunction = (valueContent' -> FunctionC callee) } =
  transitiveReturnTransfer f s callee args
returnValueTransfer f s InvokeInst { invokeArguments = (map fst -> args)
                                        , invokeFunction = (valueContent' -> FunctionC callee) } =
  transitiveReturnTransfer f s callee args
returnValueTransfer f s i = return $ fromMaybe s $ do
  p <- accessPath i
  let absPath = abstractAccessPath p
      addArg aid =
        let v = S.singleton (aid, absPath)
        in (sapReturns %~ M.insertWith S.union f v) s
  case valueContent' (accessPathBaseValue p) of
    ArgumentC a -> return $ addArg (argumentIndex a)
--      return $ maybe s addArg (M.lookup a aids)
    _ -> return s


valuesAsInsts :: [Value] -> [Instruction]
valuesAsInsts = mapMaybe toInst
  where
    toInst v =
      case valueContent' v of
        InstructionC i -> Just i
        _ -> Nothing

accessPathBaseArgument :: AccessPath -> Maybe Argument
accessPathBaseArgument p =
  case valueContent' (accessPathBaseValue p) of
    ArgumentC a -> return a
    _ -> Nothing

toInstruction :: Value -> Maybe Instruction
toInstruction v =
  case valueContent' v of
    InstructionC i -> return i
    _ -> Nothing

safeIndex :: Int -> [a] -> Maybe a
safeIndex ix lst | ix >= length lst = Nothing
                 | otherwise = return $ lst !! ix
