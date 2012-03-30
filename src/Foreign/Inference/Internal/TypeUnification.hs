{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE TemplateHaskell, FlexibleContexts #-}
{-|

In LLVM 3, the same type can have different names (with .NNN suffixes)
in different compilation units.  Sometimes types with the same name
prefix are actually not the same.  This modules performs structural
unification over types to determine which are equal.

-}
module Foreign.Inference.Internal.TypeUnification (
  unifyTypes
  ) where

import Control.Monad.Trans.Class
import Control.Monad.Error.Class
import Control.Monad.Identity
import Control.Monad.EitherK
import Control.Unification
import Control.Unification.IntVar
import Data.Foldable ( Foldable )
import Data.Traversable ( Traversable )
import Data.HashSet ( HashSet )
import qualified Data.HashSet as HS
import Data.HashMap.Strict ( HashMap )
import qualified Data.HashMap.Strict as HM
import Data.List ( find, foldl' )
import Debug.Trace.LocationTH
import Text.Regex.TDFA

import LLVM.Analysis

-- This is adapted from one of the tests in unification-fd

-- | A type of Type terms
data T a = T String [a]
         deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

instance Unifiable T where
  zipMatch (T a xs) (T b ys) =
    case a == b of
      True -> fmap (T a) (pair xs ys)
      False -> Nothing

type TTerm = UTerm T IntVar

-- | Build a term from a name and a list of term arguments.
typeTerm :: String -> [TTerm] -> TTerm
typeTerm = (UTerm .) . T

-- | Given a list of types, return a list with no duplicates.  This
-- filters out types that are structurally equal and differ only by a
-- .NNN suffix added by the LLVM linker.
--
-- The only acceptable inputs are Struct types.  An error will be
-- thrown if this invariant is not met.
--
-- The first element of the return pair is the list of unified types
-- (including types that were already unique).  The second element is
-- the set of types that could not be unified but share names.
unifyTypes :: [Type] -> ([Type], [Type])
unifyTypes ts = foldr (unifyTopLevelType inputTypes typeGroups) ([], []) (HM.toList typeGroups)
  where
    inputTypes = HS.fromList ts
    reachedTypes = retainedTypeSearch ts
    typeGroups = groupByBaseName $ filter isStruct (HS.toList reachedTypes)

-- | Try to unify all of the types sharing a base name.  This requires
-- building terms for all of the types that the input type depends on,
-- unifying them by their name groups, and then finally unifying the
-- list of input types from this step.
unifyTopLevelType :: HashSet Type
                     -> HashMap String [Type]
                     -> (String, [Type])
                     -> ([Type], [Type])
                     -> ([Type], [Type])
unifyTopLevelType inputTypes _ (_, [ty]) (unified, ununified) =
  case ty `HS.member` inputTypes of
    -- If the type was not an input, treat it as opaque.  Other types
    -- may reference it so it needs to be available.
    False -> (unified, ty : ununified)
    True -> (ty : unified, ununified)
unifyTopLevelType inputTypes m (_, instances) acc@(unified, ununified) =
  case unifyResult of
    -- Anything that couldn't be unified can be treated as an opaque
    -- type.
    Left _ -> (unified, instances ++ ununified)
    Right _ ->
      -- Find the first representative type that was in the input list
      case find (\i -> HS.member i inputTypes) instances of
        -- The type unified, but none of its representatives was an
        -- input (i.e., the type is internal only)
        Nothing ->
          -- If there are no representatives from the input type list,
          -- just choose one and treat it as opaque/ununified.
          case instances of
            [] -> acc
            repr : _ -> (unified, repr : ununified)
        Just repr -> (repr : unified, ununified)
  where
    (unifyResult, _) = runIdentity $ runIntBindingT $ do
      varMap <- assignVars m
      runEitherKT $ do
        -- For each type that instances depend on, build a term.  Unify
        -- the ones with the same base name.  Then build terms for each
        -- instance and unify those
        let primaryTerms = map (toTerm varMap) instances
            retainedTypes = retainedTypeSearch instances `HS.difference` HS.fromList instances
            dependencyTerms = groupByBaseName $ filter isStruct (HS.toList retainedTypes)
        -- Now unify all sets of used types that have the same base
        -- name
        mapM_ (unifies . map (toTerm varMap)) (map snd $ HM.toList dependencyTerms)
        unifies primaryTerms

-- | Perform a breadth-first search to discover all types referenced
-- by the given input type list
retainedTypeSearch :: [Type] -> HashSet Type
retainedTypeSearch = go HS.empty . HS.fromList
  where
    go visited q =
      let vals = q `HS.difference` visited
      in case HS.null vals of
        True -> visited
        False ->
          let visited' = visited `HS.union` vals
              q' = foldl' addValuesFrom HS.empty (HS.toList vals)
          in go visited' q'
    addValuesFrom q ty =
      case ty of
        TypeStruct _ ts _ -> q `HS.union` HS.fromList ts
        TypeFunction r ts _ -> q `HS.union` HS.fromList (r : ts)
        TypeArray _ t' -> HS.insert t' q
        TypePointer t' _ -> HS.insert t' q
        _ -> HS.insert ty q

-- | Top level term creator; this only works for named structs.
toTerm :: HashMap Type TTerm -> Type -> TTerm
toTerm m ty@(TypeStruct (Just name) members _) =
  typeTerm sname (svar : map (toTerm' m) members)
  where
    Just svar = HM.lookup ty m
    sname = structBaseName name
toTerm _ ty = $failure $ "Expected struct type: " ++ show ty

-- | Inner term creator; for structs, just return the variable
-- assigned to that Type.
toTerm' :: HashMap Type TTerm -> Type -> TTerm
toTerm' m (TypePointer ty _) = typeTerm "*" [toTerm' m ty]
toTerm' m ty@(TypeStruct (Just name) members _) =
  HM.lookupDefault ($failure ("Expected variable: " ++ show ty)) ty m
toTerm' m (TypeStruct Nothing members _) =
  typeTerm "%primitive.anonstruct" (map (toTerm' m) members)
toTerm' _ (TypeInteger i) = typeTerm ("%primitive.i" ++ show i) []
toTerm' _ TypeFloat = typeTerm "%primitive.float" []
toTerm' _ TypeDouble = typeTerm "%primitive.double" []
toTerm' m (TypeFunction r ts _) =
  typeTerm "%primitive.function" (map (toTerm' m) (r : ts))
toTerm' m (TypeArray _ ty) = typeTerm "%primitive.array" [toTerm' m ty]
toTerm' _ TypeVoid = typeTerm "%primitive.void" []
toTerm' _ TypeX86FP80 = typeTerm "%primitive.x86_fp80" []
toTerm' _ ty = $failure ("Unexpected type: " ++ show ty)

-- | Assign fresh unification variables to every struct type in the
-- input map.
assignVars :: HashMap String [Type] -> IntBindingT T Identity (HashMap Type TTerm)
assignVars = foldM assignVarL HM.empty . HM.toList
  where
    assignVarL acc (_, ts) = foldM assignVar acc ts
    assignVar acc ty = do
      x <- freeVar
      return $! HM.insert ty (UVar x) acc

-- | Take a list of types and group them by their base names (that is,
-- the part of the name up to the trailing .NNN).
groupByBaseName :: [Type] -> HashMap String [Type]
groupByBaseName = foldr addToMap HM.empty
  where
    addToMap ty@(TypeStruct (Just name) _ _) m =
      HM.insertWith (++) (structBaseName name) [ty] m
    addToMap ty _ = $failure $ "Expected TypeStruct, got " ++ show ty

-- | Strip any trailing .NNN suffix from the string.
structBaseName :: String -> String
structBaseName n =
  case captures of
    [] -> $failure $ "Unexpected undecomposable struct name: " ++ n
    [pfx] -> pfx
    [pfx,_] -> pfx
    _ -> $failure $ "Unexpected undecomposable struct name: " ++ n
  where
    m :: (String, String, String, [String])
    m@(_, _, _, captures) = n =~ "([[:alpha:]]+\\.[[:alnum:]_]+)(\\.[[:digit:]]+)?"

-- | Unify a list of terms
unifies :: (Functor (e m), BindingMonad t v m, MonadTrans e, MonadError (UnificationFailure t v) (e m))
           => [UTerm t v] -> e m ()
unifies [] = return ()
unifies [_] = return ()
unifies (y:ys) = go ys y
  where
    go [] _ = return ()
    go (x:xs) z = unify x z >>= go xs

-- Helpers

-- | Like zip, but only returns a result if the two input lists are
-- the same length
pair :: [a] -> [b] -> Maybe [(a, b)]
pair xs ys =
  case length xs == length ys of
    False -> Nothing
    True -> Just (zip xs ys)

isStruct :: Type -> Bool
isStruct (TypeStruct (Just _) _ _) = True
isStruct _ = False