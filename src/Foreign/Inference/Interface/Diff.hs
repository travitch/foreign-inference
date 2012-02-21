module Foreign.Inference.Interface.Diff (
  LibraryDiff(..),
  FunctionDiff(..),
  ParameterDiff(..),
  libraryDiff,
  emptyLibraryDiff,
  diffToByteString
  ) where

import Blaze.ByteString.Builder
import Blaze.ByteString.Builder.Char.Utf8
import Control.Arrow
import Data.ByteString.Char8 ( ByteString, unpack )
import qualified Data.ByteString.Lazy as LBS
import Data.Monoid
import Data.Map ( Map )
import qualified Data.Map as M
import Data.Maybe ( isNothing )
import Data.Set ( Set )
import qualified Data.Set as S

import Foreign.Inference.Interface

data NameChange = SameName String
                | DiffName String String
                deriving (Eq, Ord)

data TypeChange = SameType CType
                | DiffType CType CType
                deriving (Eq, Ord)

instance Show NameChange where
  show (SameName s) = s
  show (DiffName s1 s2) = concat [ s1, " -> ", s2 ]

instance Show TypeChange where
  show (SameType _) = ""
  show (DiffType t1 t2) = concat [" ", show t1, " -> ", show t2 ]

data ParameterDiff =
  ParameterDiff { parameterDiffAddedAnnotations :: [ParamAnnotation]
                , parameterDiffRemovedAnnotations :: [ParamAnnotation]
                , parameterDiffNameChange :: NameChange
                , parameterDiffTypeChange :: TypeChange
                }
  deriving (Eq, Ord)

data FunctionDiff =
  FunctionDiff { functionDiffAddedAnnotations :: [FuncAnnotation]
               , functionDiffRemovedAnnotations :: [FuncAnnotation]
               , functionDiffChangedParameters :: [Maybe ParameterDiff]
               }
  deriving (Eq, Ord)

data LibraryDiff =
  LibraryDiff { libraryDiffAddedFunctions :: [ForeignFunction]
              , libraryDiffRemovedFunctions :: [ForeignFunction]
              , libraryDiffChangedFunctions :: [(String, FunctionDiff)]
              }
  deriving (Eq, Ord)

libraryDiff :: LibraryInterface -> LibraryInterface -> LibraryDiff
libraryDiff l1 l2 =
  LibraryDiff { libraryDiffRemovedFunctions = only1
              , libraryDiffAddedFunctions = only2
              , libraryDiffChangedFunctions =
                foldr computeFuncDiffs [] inBoth
              }
  where
    (only1, only2, inBoth) = splitFunctions l1 l2

emptyLibraryDiff :: LibraryDiff
emptyLibraryDiff = LibraryDiff [] [] []

computeFuncDiffs :: (ForeignFunction, ForeignFunction)
                    -> [(String, FunctionDiff)]
                    -> [(String, FunctionDiff)]
computeFuncDiffs (f1, f2) acc =
  case diffFunc f1 f2 of
    Nothing -> acc
    Just d ->
      let name = unpack (foreignFunctionName f1)
      in (name, d) : acc

paramsDiffer :: (Parameter, Parameter) -> Maybe ParameterDiff
paramsDiffer (p1, p2) =
  case a1 == a2 && not oc of
    True -> Nothing
    False -> Just ParameterDiff { parameterDiffAddedAnnotations =
                                     S.toList $ a2 `S.difference` a1
                                , parameterDiffRemovedAnnotations =
                                  S.toList $ a1 `S.difference` a2
                                , parameterDiffNameChange = nc
                                , parameterDiffTypeChange = tc
                                }
  where
    a1 = S.fromList (parameterAnnotations p1)
    a2 = S.fromList (parameterAnnotations p2)
    naCh = parameterName p1 /= parameterName p2
    tyCh = parameterType p1 /= parameterType p2
    oc = naCh || tyCh
    nc = case naCh of
      True -> DiffName (parameterName p1) (parameterName p2)
      False -> SameName (parameterName p1)
    tc = case tyCh of
      True -> DiffType (parameterType p1) (parameterType p2)
      False -> SameType (parameterType p1)

diffFunc :: ForeignFunction -> ForeignFunction -> Maybe FunctionDiff
diffFunc f1 f2 =
  case null newAnnots && null oldAnnots && all isNothing paramDiffs of
    True -> Nothing
    False -> Just FunctionDiff { functionDiffAddedAnnotations = newAnnots
                               , functionDiffRemovedAnnotations = oldAnnots
                               , functionDiffChangedParameters = paramDiffs
                               }
  where
    a1 = S.fromList (foreignFunctionAnnotations f1)
    a2 = S.fromList (foreignFunctionAnnotations f2)
    p1 = foreignFunctionParameters f1
    p2 = foreignFunctionParameters f2

    newAnnots = S.toList $ a2 `S.difference` a1
    oldAnnots = S.toList $ a1 `S.difference` a2
    paramDiffs = map paramsDiffer (zip p1 p2)

-- | Given two library interfaces, divide the functions defined in them into three
-- categories:
--
--  1) The functions in only the first library
--
--  2) The functions in only the second library
--
--  3) The functions in both libraries
splitFunctions :: LibraryInterface -> LibraryInterface
                  -> ([ForeignFunction], [ForeignFunction], [(ForeignFunction, ForeignFunction)])
splitFunctions l1 l2 =
  let inBoth1 = S.foldr (checkInBoth f2) S.empty f1
      inBoth2 = S.foldr (checkInBoth f1) inBoth1 f2
  in (filter (notInBoth inBoth2) (libraryFunctions l1),
      filter (notInBoth inBoth2) (libraryFunctions l2),
      S.foldr (matchOldAndNew m1 m2) [] inBoth2)
  where
    f1 = S.fromList $ map foreignFunctionName (libraryFunctions l1)
    f2 = S.fromList $ map foreignFunctionName (libraryFunctions l2)
    -- m1 and m2 are mappings from function names to their foreign
    -- function defs
    toM = foreignFunctionName &&& id
    m1 = M.fromList $ map toM (libraryFunctions l1)
    m2 = M.fromList $ map toM (libraryFunctions l2)

matchOldAndNew :: (Ord k) => Map k t1 -> Map k t2 -> k -> [(t1, t2)] -> [(t1, t2)]
matchOldAndNew m1 m2 fname acc =
  (m1 M.! fname, m2 M.! fname) : acc

checkInBoth :: (Ord a) => Set a -> a -> Set a -> Set a
checkInBoth s fname inBoth =
  case fname `S.member` s of
    True -> S.insert fname inBoth
    False -> inBoth

notInBoth :: Set ByteString -> ForeignFunction -> Bool
notInBoth inBoth func =
  not (S.member (foreignFunctionName func) inBoth)





-- Bytestring conversion

-- | Build a (lazy) ByteString representation of the given diff.
diffToByteString :: LibraryDiff -> LBS.ByteString
diffToByteString = toLazyByteString . diffBuilder

diffBuilder :: LibraryDiff -> Builder
diffBuilder d = mconcat [ addedFuncs, removedFuncs, changes ]
  where
    addedFuncs = diffAddRem "Added functions:\n" (libraryDiffAddedFunctions d)
    removedFuncs = diffAddRem "Removed functions:\n" (libraryDiffRemovedFunctions d)
    changes = diffChanges (libraryDiffChangedFunctions d)

diffAddRem :: String -> [ForeignFunction] -> Builder
diffAddRem _ [] = mempty
diffAddRem s fs = mconcat $ (fromString s) : map funcToBuilder fs

funcToBuilder :: ForeignFunction -> Builder
funcToBuilder ff = mconcat [ fromString " * "
                           , fromByteString name
                           , fromString "\n"
                           ]
  where
    name = foreignFunctionName ff

diffChanges :: [(String, FunctionDiff)] -> Builder
diffChanges diffs =
  mconcat $ fromString "Changed functions:\n" : map changeToBuilder diffs

changeToBuilder :: (String, FunctionDiff) -> Builder
changeToBuilder (f, d) = mconcat $
  fromString (" * " ++ f) : added : removed : fromString "\n" : map paramChangeBuilder changed
  where
    changed = functionDiffChangedParameters d
    newAttrs = functionDiffAddedAnnotations d
    oldAttrs = functionDiffRemovedAnnotations d
    added = fromString $ concatMap (\attr -> "+" ++ show attr) newAttrs
    removed = fromString $ concatMap (\attr -> "-" ++ show attr) oldAttrs

paramChangeBuilder :: Maybe ParameterDiff -> Builder
paramChangeBuilder Nothing = mempty
paramChangeBuilder (Just d) = mconcat $ [
  fromString (concat [ "   ** "
                     , show (parameterDiffNameChange d)
                     , show (parameterDiffTypeChange d)
                     , " "
                     ]),
  fromString $ concatMap (\attr -> "+" ++ show attr) newAnnots,
  fromString $ concatMap (\attr -> "-" ++ show attr) oldAnnots
  ]
  where
    newAnnots = parameterDiffAddedAnnotations d
    oldAnnots = parameterDiffRemovedAnnotations d
