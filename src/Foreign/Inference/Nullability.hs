module Foreign.Inference.Nullability (
  -- * Types
  NullabilityAnalysis(notNullablePtrs, errorPtrs),
  -- * Constructor
  emptyNullabilityAnalysis
  ) where

import Algebra.Lattice
import Data.List ( foldl' )
import Data.LLVM.CFG
import Data.LLVM.Types
import Data.LLVM.Analysis.Dataflow
import Data.Set ( Set )
import qualified Data.Set as S

data NullabilityAnalysis =
  NA { nullPtrs :: Set Value
     , notNullPtrs :: Set Value
     , notNullablePtrs :: Set Value
     , errorPtrs :: Set Value
     }
  | Top
  deriving (Show, Eq)

emptyNullabilityAnalysis :: NullabilityAnalysis
emptyNullabilityAnalysis =
  NA { nullPtrs = S.empty
     , notNullPtrs = S.empty
     , notNullablePtrs = S.empty
     , errorPtrs = S.empty
     }

instance MeetSemiLattice NullabilityAnalysis where
  meet Top s = s
  meet s Top = s
  meet s1 s2 = NA { nullPtrs = nullPtrs s1 `S.intersection` nullPtrs s2
                  , notNullPtrs = notNullPtrs s1 `S.intersection` notNullPtrs s2
                  , notNullablePtrs = notNullablePtrs s1 `S.union` notNullablePtrs s2
                  , errorPtrs = errorPtrs s1 `S.union` errorPtrs s2
                  }

instance BoundedMeetSemiLattice NullabilityAnalysis where
  top = Top

instance DataflowAnalysis NullabilityAnalysis where
  transfer = transferFunc

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
            S.member p (notNullPtrs na')) of
        (True, _) -> na' { errorPtrs = p `S.insert` errorPtrs na' }
        (_, False) -> na' { notNullablePtrs = p `S.insert` notNullablePtrs na' }
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
