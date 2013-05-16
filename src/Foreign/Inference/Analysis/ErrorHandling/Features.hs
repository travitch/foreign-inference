{-# LANGUAGE PatternGuards, DeriveGeneric, TemplateHaskell #-}
-- | This module computes feature vectors for the error handling analysis.
--
-- The feature vectors can be used for machine learning based classification,
-- or more ad-hoc approaches.  The features are computed for each /called
-- function @f@/ in the library.  We currently use the following features:
--
--  * Number of times @f@ is called in a context known to respond to an error
--
--  * Number of times @f@ is called in a context that /cannot/ return an error
--
--  * Number of tiles @f@ is called in a context that could return an error
--
--  * Number of times @f@ is called in a context returning success
--
--  * Number of times @f@'s return value is used as an argument
--
--  * Number of times @f@'s return value is used as an argument in an error context
--
-- Each of these features is a count, which is difficult to compare
-- between libraries.  Each one is normalized (by the number of functions that
-- could possibly return an error code).
module Foreign.Inference.Analysis.ErrorHandling.Features (
  BaseFact(..),
  BasicFacts,
  ErrorFuncClass(..),
  FeatureVector,
  computeFeatures,
  classifyErrorFunctions,
  featureVectorLength,
  defaultClassifier,
  directCallTarget
  ) where

import GHC.Generics

import Control.DeepSeq
import Control.DeepSeq.Generics ( genericRnf )
import Control.Lens ( makeLenses, (%~), (^.) )
import Data.Binary
import qualified Data.Foldable as F
import Data.Map ( Map )
import qualified Data.Map as M
import Data.Maybe ( fromMaybe )
import Data.Monoid
import Data.Set ( Set )
import qualified Data.Set as S
import Data.Vector.Unboxed ( Vector )
import qualified Data.Vector.Unboxed as UV

import LLVM.Analysis
import LLVM.Analysis.BlockReturnValue

import Foreign.Inference.Internal.FlattenValue

data Feature = Feature { _calledInErrorContext :: Int
                       , _calledInNonErrorContext :: Int
                       , _calledInPossibleErrorContext :: Int
                       , _calledInSuccessContext :: Int
                       , _usedAsArgument :: Int
                       , _usedAsArgumentInErrorContext :: Int
                       }
$(makeLenses ''Feature)
emptyFeature :: Feature
emptyFeature = Feature 0 0 0 0 0 0
{-
addCalledInErrorContext = emptyFeature { calledInErrorContext = 1 }
addCalledInNonErrorContext = emptyFeature { calledInNonErrorContext = 1 }
addCalledInPossibleErrorContext = emptyFeature { calledInPossibleErrorContext = 1 }
addCalledInSuccessContext = emptyFeature { calledInSuccessContext = 1 }
addUsedAsArgument = emptyFeature { usedAsArgument = 1 }
addUsedAsArgumentInErrorContext = emptyFeature { usedAsArgumentInErrorContext = 1 }

instance Monoid Feature where
  mempty = emptyFeature
  mappend f1 f2 =
    Feature { calledInErrorContext = calledInErrorContext f1 + calledInErrorContext f2
            , calledInNonErrorContext = calledInNonErrorContext f1 + calledInNonErrorContext f2
            , calledInPossibleErrorContext = calledInPossibleErrorContext f1 + calledInPossibleErrorContext f2
            , calledInSuccessContext = calledInSuccessContext f1 + calledInSuccessContext f2
            , usedAsArgument = usedAsArgument f1 + usedAsArgument f2
            , usedAsArgumentInErrorContext = usedAsArgumentInErrorContext f1 + usedAsArgumentInErrorContext f2
            }
-}

update :: (Feature -> Feature) -> Maybe Feature -> Maybe Feature
update modifier f = Just . modifier $ fromMaybe emptyFeature f


data BaseFact = ErrorBlock (Set Value)
              -- ^ For a block returning an error code, record the error
              -- descriptor and the set of functions used as arguments to
              -- other functions.
              | SuccessBlock
              -- ^ Records the functions called in a block that reports
              -- success.
              deriving (Generic, Eq, Ord)

instance NFData BaseFact where
  rnf = genericRnf

-- For each block, record its error descriptor (if any).  Also include the
-- "ignored" values - those values used as function arguments in that block.
--
-- If a block is not present in this map, it does not report errors or
-- successes (as far as we know so far)
type BasicFacts = Map BasicBlock BaseFact
data ErrorFuncClass = ErrorReporter
                    | OtherFunction
                    deriving (Eq, Ord, Show)

-- | This Binary instance maps the labels to Bool.  This instance
-- is required to serialize the SVM classifier.
instance Binary ErrorFuncClass where
  put ErrorReporter = put True
  put OtherFunction = put False
  get = do
    b <- get
    if b then return ErrorReporter else return OtherFunction

type FeatureVector = Vector Double



-- instance Monoid Feature where
--   mempty = Feature 0 0 0 0
--   mappend (Feature ne1 e1 s1 a1) (Feature ne2 e2 s2 a2) =
--     Feature (ne1 + ne2) (e1 + e2) (s1 + s2) (a1 + a2)

-- FIXME: count uses of each function *not* in a function returning an int.
-- Also count uses of each function in functions returning an int.
--
-- Better: functions that return int32, but can return more than one possible
-- value.

-- | Iterate over every BasicBlock in the library.  If the basic block is not
-- in BasicFacts, we don't believe it is an error handling context, so
-- increment the notError count for each of its called functions.
computeFeatures :: (HasFunction funcLike, HasBlockReturns funcLike)
                => BasicFacts
                -> [funcLike]
                -> Map Value FeatureVector
computeFeatures bf funcs =
  fmap (toFeatureVector nBlocks nSuccBlocks nErrBlocks nIntFuncs) m
  where
    (succMap, errMap) = M.partition (==SuccessBlock) bf
    m = F.foldl' (computeFuncFeatures bf) mempty funcs
    nBlocks = M.size m
    nSuccBlocks = M.size succMap
    nErrBlocks = M.size errMap

    nIntFuncs = F.foldl' countIntReturns 0 funcs
    countIntReturns acc f = if complexIntFunction f then acc + 1 else acc

-- | Returns True if the input Function is of type Int and can return
-- more than one value.  This is a reasonable approximation of functions
-- that could possibly returning an error code.
complexIntFunction :: (HasFunction funcLike)
                   => funcLike -> Bool
complexIntFunction funcLike =
  case functionReturnType f of
    TypeInteger _ -> length (exitValues f) > 1
    _ -> False
  where
    f = getFunction funcLike

exitValues :: Function -> [Value]
exitValues f = concatMap fromReturn exitInsts
  where
    exitInsts = functionExitInstructions f
    fromReturn i =
      case i of
        RetInst { retInstValue = Just rv } -> flattenValue rv
        _ -> []


featureVectorLength :: Double
featureVectorLength =
  fromIntegral $ UV.length $ toFeatureVector 1 1 1 1 emptyFeature

defaultClassifier :: FeatureVector -> ErrorFuncClass
defaultClassifier fv
  | fv UV.! 0 > 0.5 && fv UV.! 2 == 0 = ErrorReporter
  | otherwise = OtherFunction

-- | More values needed for useful features:
--
-- Try to use only blocks/functions we know are returning errors.
-- Reasoning about the rest of the code like this is pretty dangerous.
-- We can't say much one way or the other.
--
toFeatureVector :: Int -> Int -> Int -> Int -> Feature -> FeatureVector
toFeatureVector nBlocks nSuccBlocks nErrBlocks nIntFuncs f = UV.map normalize $
  UV.fromList [ fromIntegral (f ^. calledInErrorContext) / fromIntegral nErrBlocks
              -- , fromIntegral (f ^. calledInNonErrorContext) / fromIntegral nIntFuncs
              , fromIntegral (f ^. calledInSuccessContext) / fromIntegral nSuccBlocks
              -- , fromIntegral (f ^. calledInPossibleErrorContext) / fromIntegral nIntFuncs
              , min 1 (fromIntegral (f ^. usedAsArgumentInErrorContext))
              , fromIntegral (f ^. calledInSuccessContext) / fromIntegral (f ^. calledInErrorContext)
              -- , fromIntegral (f ^. calledInErrorContext) / fromIntegral (f ^. calledInNonErrorContext)
              -- , fromIntegral (f ^. calledInPossibleErrorContext) / fromIntegral (f ^. calledInNonErrorContext)
              ]
              {-
  UV.fromList [ fromIntegral (f ^. calledInErrorContext) / fromIntegral nIntFuncs
              , fromIntegral (f ^. calledInNonErrorContext) / fromIntegral nIntFuncs
              , fromIntegral (f ^. calledInSuccessContext) / fromIntegral nIntFuncs
              , fromIntegral (f ^. calledInPossibleErrorContext) / fromIntegral nIntFuncs
              , min 1 (fromIntegral (f ^. usedAsArgumentInErrorContext))
              , fromIntegral (f ^. calledInErrorContext) / fromIntegral (f ^. calledInPossibleErrorContext)
              , fromIntegral (f ^. calledInErrorContext) / fromIntegral (f ^. calledInNonErrorContext)
              , fromIntegral (f ^. calledInPossibleErrorContext) / fromIntegral (f ^. calledInNonErrorContext)
              ]
-}
normalize :: Double -> Double
normalize d
  | isInfinite d || isNaN d = 0.0
  | otherwise = d

-- (Feature nerr inerr insucc arg _ _) =
  -- UV.fromList [ fromIntegral nerr / fromIntegral nFuncs
  --             , fromIntegral inerr / fromIntegral nFuncs
  --             , fromIntegral insucc / fromIntegral nFuncs
  --             , fromIntegral arg / fromIntegral nFuncs
  --             , fromIntegral inerr / fromIntegral nerr
  --             ]

-- compute block returns here - if there is a constant return
-- value, classify it as a possible error context
computeFuncFeatures :: (HasFunction funcLike, HasBlockReturns funcLike)
                    => BasicFacts
                    -> Map Value Feature
                    -> funcLike
                    -> Map Value Feature
computeFuncFeatures bf m funcLike =
  F.foldl' (computeBlockFeatures bf isComplex) m (functionBody f)
  where
    isComplex = complexIntFunction funcLike
    f = getFunction funcLike
    -- brs = getBlockReturns funcLike

computeBlockFeatures :: BasicFacts
                     -> Bool
                     -> Map Value Feature
                     -> BasicBlock
                     -> Map Value Feature
computeBlockFeatures bf isComplex m bb
  | Just baseFact <- M.lookup bb bf =
    F.foldl' (calleeInContext baseFact) m (basicBlockInstructions bb)
  | otherwise = F.foldl' (calleeNotError isComplex) m (basicBlockInstructions bb)

calleeInContext :: BaseFact -> Map Value Feature
                -> Instruction -> Map Value Feature
calleeInContext SuccessBlock m i
  | Just cv <- directCallTarget i =
    M.alter (update (calledInSuccessContext %~ (+1))) cv m
  | otherwise = m
calleeInContext (ErrorBlock args) m i
  | Just cv <- directCallTarget i, S.member (toValue i) args =
    M.alter (update (usedAsArgumentInErrorContext %~ (+1))) cv m
  | Just cv <- directCallTarget i =
    M.alter (update (calledInErrorContext %~ (+1))) cv m
  | otherwise = m


calleeNotError :: Bool -> Map Value Feature -> Instruction -> Map Value Feature
calleeNotError isComplex m i
  | Just cv <- directCallTarget i
  , isComplex = M.alter (update (calledInPossibleErrorContext %~ (+1))) cv m
  | Just cv <- directCallTarget i
  , not isComplex = M.alter (update (calledInNonErrorContext %~ (+1))) cv m
  | otherwise = m

-- | If the value is a call inst to a known function (external or locally defined),
-- return the target
directCallTarget :: Instruction -> Maybe Value
directCallTarget v =
  case v of
    CallInst { callFunction = cv } ->
      case valueContent' cv of
        ExternalFunctionC _ -> return (stripBitcasts cv)
        FunctionC _ -> return (stripBitcasts cv)
        _ -> fail "Not a direct call"
    _ -> fail "Not a call"

-- | Compute the features for each called value in the library (using
-- the BasicFacts and funcLikes).  Classify each one using the classifier.
-- Insert each 'ErrorReporter' into the result set.
classifyErrorFunctions :: (HasFunction funcLike, HasBlockReturns funcLike)
                       => BasicFacts
                       -> [funcLike]
                       -> (FeatureVector -> ErrorFuncClass)
                       -> Set Value
classifyErrorFunctions facts funcs classifier =
  F.foldl' classifyValue mempty features
  where
    features = M.toList (computeFeatures facts funcs)
    classifyValue acc (val, featureVec) =
      case classifier featureVec of
        ErrorReporter -> S.insert val acc
        OtherFunction -> acc

