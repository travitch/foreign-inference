{-# LANGUAGE PatternGuards, DeriveGeneric #-}
module Foreign.Inference.Analysis.ErrorHandling.Features (
  BaseFact(..),
  BasicFacts,
  ErrorFuncClass(..),
  FeatureVector,
  computeFeatures,
  classifyErrorFunctions,
  featureVectorLength
  ) where

import GHC.Generics

import Control.DeepSeq
import Control.DeepSeq.Generics ( genericRnf )
import Data.Binary
import qualified Data.Foldable as F
import Data.Map ( Map )
import qualified Data.Map as M
import Data.Monoid
import Data.Set ( Set )
import qualified Data.Set as S
import Data.Vector.Unboxed ( Vector )
import qualified Data.Vector.Unboxed as UV

import LLVM.Analysis

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

data Feature = Feature { notError :: Int
                       , inError :: Int
                       , inSuccess :: Int
                       , argInError :: Int
                       }

instance Monoid Feature where
  mempty = Feature 0 0 0 0
  mappend (Feature ne1 e1 s1 a1) (Feature ne2 e2 s2 a2) =
    Feature (ne1 + ne2) (e1 + e2) (s1 + s2) (a1 + a2)

-- | Iterate over every BasicBlock in the library.  If the basic block is not
-- in BasicFacts, we don't believe it is an error handling context, so
-- increment the notError count for each of its called functions.
computeFeatures :: (HasFunction funcLike)
                => BasicFacts
                -> [funcLike]
                -> Map Value FeatureVector
computeFeatures bf funcs =
  fmap (toFeatureVector nFuncs) m
  where
    m = F.foldl' (computeFuncFeatures bf) mempty fs
    fs = map getFunction funcs
    nFuncs = M.size m

featureVectorLength :: Double
featureVectorLength = 5.0

toFeatureVector :: Int -> Feature -> FeatureVector
toFeatureVector nFuncs (Feature nerr inerr insucc arg) =
  UV.fromList [ fromIntegral nerr / fromIntegral nFuncs
              , fromIntegral inerr / fromIntegral nFuncs
              , fromIntegral insucc / fromIntegral nFuncs
              , fromIntegral arg / fromIntegral nFuncs
              , fromIntegral inerr / fromIntegral nerr
              ]

computeFuncFeatures :: BasicFacts
                    -> Map Value Feature
                    -> Function
                    -> Map Value Feature
computeFuncFeatures bf m f =
  F.foldl' (computeBlockFeatures bf) m (functionBody f)

computeBlockFeatures :: BasicFacts
                     -> Map Value Feature
                     -> BasicBlock
                     -> Map Value Feature
computeBlockFeatures bf m bb
  | Just baseFact <- M.lookup bb bf =
    F.foldl' (calleeInContext baseFact) m (basicBlockInstructions bb)
  | otherwise = F.foldl' calleeNotError m (basicBlockInstructions bb)

calleeInContext :: BaseFact -> Map Value Feature
                -> Instruction -> Map Value Feature
calleeInContext SuccessBlock m i
  | Just cv <- directCallTarget i =
    M.insertWith mappend cv succVal m
  | otherwise = m
calleeInContext (ErrorBlock args) m i
  | Just cv <- directCallTarget i, S.member cv args =
    M.insertWith mappend cv argVal m
  | Just cv <- directCallTarget i =
    M.insertWith mappend cv errVal m
  | otherwise = m

-- Maybe the reason archive looks weird is that no references to errno
-- come in blocks with known errors from the first pass?  Test this?
--
-- It looks like errno really is accessed, so there is some bug in
-- maintaining the used-as-args set that we wanted to use to compute
-- features.
--
-- It might be that the particular *blocks* in which errno is accessed
-- are not recognized...

succVal :: Feature
succVal = mempty { inSuccess = 1 }
errVal :: Feature
errVal = mempty { inError = 1 }
argVal :: Feature
argVal = mempty { argInError = 1 }
nVal :: Feature
nVal = mempty { notError = 1 }

calleeNotError :: Map Value Feature -> Instruction -> Map Value Feature
calleeNotError m i
  | Just cv <- directCallTarget i =
    M.insertWith mappend cv nVal m
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
classifyErrorFunctions :: (HasFunction funcLike)
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


