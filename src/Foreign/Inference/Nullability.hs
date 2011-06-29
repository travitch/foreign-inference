module Foreign.Inference.Nullability (
  -- * Types
  NullabilityAnalysis(notNullablePtrs, errorPtrs, notNullableFields),
  -- * Constructor
  emptyNullabilityAnalysis
  ) where

import Algebra.Lattice
import Data.List ( foldl' )
import Data.LLVM.CFG
import Data.LLVM.Types
import Data.LLVM.Analysis.Dataflow
import Data.Hashable
import Data.HashSet ( HashSet )
import qualified Data.HashSet as S

data FieldDescriptor = FD !Type !Int
                     deriving (Show, Eq)

instance Hashable FieldDescriptor where
  hash (FD t i) = hash t `combine` i

data NullabilityAnalysis =
  NA { nullPtrs :: HashSet Value
     , notNullPtrs :: HashSet Value
     , notNullablePtrs :: HashSet Value
     , errorPtrs :: HashSet Value
     , notNullableFields :: HashSet FieldDescriptor
     }
  | Top
  deriving (Show, Eq)

emptyNullabilityAnalysis :: NullabilityAnalysis
emptyNullabilityAnalysis =
  NA { nullPtrs = S.empty
     , notNullPtrs = S.empty
     , notNullablePtrs = S.empty
     , errorPtrs = S.empty
     , notNullableFields = S.empty
     }

instance MeetSemiLattice NullabilityAnalysis where
  meet Top s = s
  meet s Top = s
  meet s1 s2 = NA { nullPtrs = nullPtrs s1 `S.intersection` nullPtrs s2
                  , notNullPtrs = notNullPtrs s1 `S.intersection` notNullPtrs s2
                  , notNullablePtrs = notNullablePtrs s1 `S.union` notNullablePtrs s2
                  , errorPtrs = errorPtrs s1 `S.union` errorPtrs s2
                  , notNullableFields = notNullableFields s1 `S.union` notNullableFields s2
                  }

instance BoundedMeetSemiLattice NullabilityAnalysis where
  top = Top

instance DataflowAnalysis NullabilityAnalysis where
  transfer = transferFunc

-- Can ignore the first index in the GEP, since it just deals with
-- selecting top-level objects from a base address.  They are all of
-- the same type.  The rest of the indices delve down.
fieldAccessInfo :: Value -> Maybe FieldDescriptor
fieldAccessInfo Value { valueContent =
                           gep@GetElementPtrInst {
                             getElementPtrValue = v@Value { valueType = TypePointer it _ }
                             , getElementPtrIndices = _:ixs
                             }
                      } = gepStructField it ixs
  where
    gepStructField :: Type -> [Value] -> Maybe FieldDescriptor
    -- Put this one first since we always want to step through a named
    -- type, regardless of its indices
    gepStructField (TypeNamed _ it) indices = gepStructField it indices
    -- This is the case we care about - the last index in a GEP into a
    -- struct type.  This is the field that is not nullable.
    gepStructField st@(TypeStruct its _) [Value { valueContent = ConstantInt ix }] =
      case length its > fromIntegral ix of
        True -> Just $ FD st (fromIntegral ix)
        False -> error "GEP index greater than struct type list length"
    -- This could happen if the last index is not constant or the
    -- current "base" isn't a struct type.
    gepStructField _ [_] = Nothing
    -- Otherwise, step through the index for this type
    gepStructField (TypeArray _ it) (_:rest) = gepStructField it rest
    gepStructField (TypePointer it _) (_:rest) = gepStructField it rest
    -- We can only resolve constant ints - it is probably an error to
    -- have a non-constant here with a struct type anyway.
    gepStructField (TypeStruct its _) ((Value {valueContent = ConstantInt ix}):rest) =
      case length its > fromIntegral ix of
        True -> gepStructField (its !! fromIntegral ix) rest
        False -> error "GEP index greater than struct type list length"
    gepStructField _ _ = Nothing
fieldAccessInfo _ = Nothing

-- | If this is a successor of a null test, add a fact.  This probably
-- also needs to handle getElementPtr, though that really only
-- calculates addresses.  Really, this will have to consult the
-- results of an alias analysis.
transferFunc :: NullabilityAnalysis -> Value -> [EdgeCondition] -> NullabilityAnalysis
transferFunc na v edges = maybe na' addDerefInfo dereferencedPtr
  where
    na' = addEdgeInformation edges

    addDerefInfo p =
      case (S.member p (nullPtrs na'),
            S.member p (notNullPtrs na'),
            fieldAccessInfo p) of
        (True, _, _) -> na' { errorPtrs = p `S.insert` errorPtrs na' }
        (_, False, Nothing) -> na' { notNullablePtrs = p `S.insert` notNullablePtrs na' }
        (_, False, Just fi) -> na' { notNullablePtrs = p `S.insert` notNullablePtrs na'
                                   , notNullableFields = fi `S.insert` notNullableFields na'
                                   }
        _ -> na'

    dereferencedPtr = case valueContent v of
      StoreInst { storeAddress = dest@Value { valueType = TypePointer _ _ } } -> Just dest
      LoadInst { loadAddress = src@Value { valueType = TypePointer _ _ } } -> Just src
      _ -> Nothing


    addEdgeInformation = foldl' processEdge na
    -- Ignore floating point comparisons - only integer comparisons
    -- are used for pointers.
    processEdge n (TrueEdge cmp) = case valueContent cmp of
      ICmpInst ICmpEq v1 Value { valueContent = ConstantPointerNull } ->
        -- v1 is null
        n { nullPtrs = v1 `S.insert` nullPtrs n }
      ICmpInst ICmpEq Value { valueContent = ConstantPointerNull } v2 ->
        -- v2 is null
        n { nullPtrs = v2 `S.insert` nullPtrs n }
      ICmpInst ICmpNe v1 Value { valueContent = ConstantPointerNull } ->
        -- v1 is not null
        n { notNullPtrs = v1 `S.insert` notNullPtrs n }
      ICmpInst ICmpNe Value { valueContent = ConstantPointerNull } v2 ->
        -- v2 is not null
        n { notNullPtrs = v2 `S.insert` notNullPtrs n }
      _ -> n
    processEdge n (FalseEdge cmp) = case valueContent cmp of
      ICmpInst ICmpEq v1 Value { valueContent = ConstantPointerNull } ->
        -- v1 is not null
        n { notNullPtrs = v1 `S.insert` notNullPtrs n }
      ICmpInst ICmpEq Value { valueContent = ConstantPointerNull } v2 ->
        -- v2 is not null
        n { notNullPtrs = v2 `S.insert` notNullPtrs n }
      ICmpInst ICmpNe v1 Value { valueContent = ConstantPointerNull } ->
        -- v1 is null
        n { nullPtrs = v1 `S.insert` nullPtrs n }
      ICmpInst ICmpNe Value { valueContent = ConstantPointerNull } v2 ->
        -- v2 is null
        n { nullPtrs = v2 `S.insert` nullPtrs n }
      _ -> n
    processEdge n _ = n
