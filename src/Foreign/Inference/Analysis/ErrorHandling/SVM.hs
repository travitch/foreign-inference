{-# LANGUAGE PatternGuards #-}
module Foreign.Inference.Analysis.ErrorHandling.SVM (
  ErrorFuncClass,
  FeatureVector,
  computeFeatures,
  classifyErrorFunctions,
  ) where

import AI.SVM.Simple
import qualified Data.Foldable as F
import Data.Map ( Map )
import qualified Data.Map as M
import Data.Monoid
import qualified Data.Set as S
import Data.Vector.Unboxed ( Vector )
import qualified Data.Vector.Unboxed as UV

data ErrorFuncClass = ErrorReporter
                    | OtherFunction
                    deriving (Eq, Ord, Show)

type FeatureVector = UV.Vector Double

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
  fmap toFeatureVector m
  where
    m = F.foldl' (computeFuncFeatures bf) mempty fs
    fs = map getFunction funcs

toFeatureVector :: Feature -> FeatureVector
toFeatureVector (Feature nerr inerr insucc arg) = undefined

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

calleeInContext SuccessBlock m i =
  | Just cv <- directCallTarget i =
    M.insertWith mappend cv succVal m
  | otherwise = m
calleeInContext (ErrorBlock args) baseFact m i
  | Just cv <- directCallTarget i, S.member cv args =
    M.insertWith mappend cv argVal m
  | Just cv <- directCallTarget i =
    M.insertWith mappend cv errVal m
  | otherwise = m

succVal = mempty { inSuccess = 1 }
errVal = mempty { inError = 1 }
argVal = mempty { argInError = 1 }
nVal = mempty { notError = 1 }

calleeNotError m i
  | Just cv <- directCallTarget i =
    M.insertWith mappend cv nVal m
  | otherwise = m

-- | If the value is a call inst to a known function (external or locally defined),
-- return the target
directCallTarget :: Instruction -> Maybe Value
directCallTarget v =
  case v of
    InstructionC CallInst { callFunction = cv } ->
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
                       -> SVMClassifier ErrorFuncClass
                       -> Set Value
classifyErrorFunctions facts funcs classifier =
  F.foldl' classifyValue mempty features
  where
    features = M.toList (computeFeatures facts funcs)
    classifyValue acc (val, featureVec) =
      case classify classifier featureVec of
        ErrorReporter -> S.insert val acc
        OtherFunction -> acc
