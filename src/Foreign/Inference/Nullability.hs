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
import Data.HashMap.Strict ( HashMap )
import Data.HashSet ( HashSet )
import qualified Data.HashSet as S
import qualified Data.HashMap.Strict as M

import Text.Printf
import Debug.Trace
debug = flip trace

data FieldDescriptor = FD !Type !Int
                     deriving (Show, Eq)

instance Hashable FieldDescriptor where
  hash (FD t i) = hash t `combine` i

data NullabilityAnalysis =
  NA { nullPtrs :: HashSet Value
     , notNullPtrs :: HashSet Value
     , nullFields :: HashMap Value FieldDescriptor
     , notNullFields :: HashMap Value FieldDescriptor
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
     , nullFields = M.empty
     , notNullFields = M.empty
     , notNullablePtrs = S.empty
     , errorPtrs = S.empty
     , notNullableFields = S.empty
     }

instance MeetSemiLattice NullabilityAnalysis where
  meet Top s = s
  meet s Top = s
  meet s1 s2 = NA { nullPtrs = nullPtrs s1 `S.intersection` nullPtrs s2
                  , notNullPtrs = notNullPtrs s1 `S.intersection` notNullPtrs s2
                  , nullFields = nullFields s1 `M.intersection` nullFields s2
                  , notNullFields = notNullFields s1 `M.intersection` notNullFields s2
                  , notNullablePtrs = notNullablePtrs s1 `S.union` notNullablePtrs s2
                  , errorPtrs = errorPtrs s1 `S.union` errorPtrs s2
                  , notNullableFields = notNullableFields s1 `S.union` notNullableFields s2
                  }

instance BoundedMeetSemiLattice NullabilityAnalysis where
  top = Top

instance DataflowAnalysis NullabilityAnalysis where
  transfer = transferFunc

-- | This function extracts a 'FieldDescriptor' from a GetElementPtr
-- instruction.  The descriptor holds information about the field that
-- is being referenced by the instruction.  GEP instructions can have
-- many indices for stepping through aggregate types; the function
-- returns the *innermost* field reference (and contains no
-- information about enclosing types).  For example, consider the following
-- structure and reference:
--
-- > struct S {
-- >   int *p1;
-- >   int *p2;
-- > };
-- >
-- > struct T {
-- >   struct S s1;
-- >   struct S s2;
-- > };
-- >
-- > struct T t;
-- > x = t.s1.p1;
--
-- This will result in a GetElementPtr instruction like the following:
--
-- > %1 = getelementptr %struct.T* %t, i32 0, i32 0, i32 0
--
-- This function will return the innermost field access: (%struct.S,
-- 0) since that is the final field being referenced.  Recording just
-- the innermost field access lets us track a smaller amount of
-- information: the named field of a struct S in /any/ context is
-- treated the same.
--
-- Note that we can ignore the first index in the GEP, since it just
-- deals with selecting top-level objects from a base address.  They
-- are all of the same type.
fieldAccessInfo :: Value -> Maybe FieldDescriptor
fieldAccessInfo Value { valueContent =
                             GetElementPtrInst {
                               getElementPtrValue = Value { valueType = TypePointer it0 _ }
                               , getElementPtrIndices = _:ixs
                               }
                        } = gepStructField it0 ixs
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

-- | This function is just a wrapper around 'fieldAccessInfo' to get
-- the information for a field access involved in a Load or Store.
-- This is used in the case that we know a field is being read from or
-- written to and we need to know which one.
addrFieldAccessInfo :: Value -> Maybe FieldDescriptor
addrFieldAccessInfo Value { valueContent = LoadInst { loadAddress = addr } } =
  fieldAccessInfo addr
addrFieldAccessInfo Value { valueContent = StoreInst { storeAddress = addr } } =
  fieldAccessInfo addr
addrFieldAccessInfo _ = Nothing

-- | If this is a successor of a null test, add a fact.  This probably
-- also needs to handle getElementPtr, though that really only
-- calculates addresses.  Really, this will have to consult the
-- results of an alias analysis.
transferFunc :: NullabilityAnalysis -> Value -> [EdgeCondition] -> NullabilityAnalysis
transferFunc na v edges = maybe na' (addDerefInfo na') (getDereferencedPtr v)
  where
    na' = foldl' addEdgeInformation na edges

-- | Add information to the anaylsis state that we gain from observing
-- a dereferenced pointer.  The basic idea (handled in several cases)
-- is that if we see a pointer that is known to be non-NULL
-- dereferenced, that pointer is nullable.  If we see a pointer that
-- is not known to be non-NULL dereferenced, that pointer is not
-- nullable (i.e., it must not be NULL to be dereferenced safely).
addDerefInfo :: NullabilityAnalysis -> Value -> NullabilityAnalysis
addDerefInfo na p =
  case (S.member p (nullPtrs na),
        S.member p (notNullPtrs na),
        addrFieldAccessInfo p,
        M.lookup p (notNullFields na)
       ) of

    -- This is an unlikely case, but here we know that a pointer is
    -- NULL and we see that it is being dereferenced.
    (True, _, _, _) -> na { errorPtrs = p `S.insert` errorPtrs na }
    (_, False, Just fi, Nothing) -> na { notNullablePtrs = p `S.insert` notNullablePtrs na
                              , notNullableFields = fi `S.insert` notNullableFields na
                              }
    -- FIXME: probably need to handle a case where there is a guard
    -- for a field of the struct, but not the one being dereferenced.
    (_, False, _, _) -> na { notNullablePtrs = p `S.insert` notNullablePtrs na }
    -- Otherwise it isn't interesting and we don't add any information
    _ -> na

-- | Get the pointer that is being dereferenced by this Load or Store
-- instruction.  If this is not a load or store instruction, just
-- return Nothing.
getDereferencedPtr :: Value -> Maybe Value
getDereferencedPtr v = case valueContent v of
  StoreInst { storeAddress = dest@Value { valueType = TypePointer _ _ } } -> Just dest
  LoadInst { loadAddress = src@Value { valueType = TypePointer _ _ } } -> Just src
  _ -> Nothing

-- | Add information about null/non null pointers to the analysis
-- state that we learn from incoming edges.  In particular, this looks
-- at edges induced by a comparison instruction followed by a branch.
-- If the comparison was comparing a pointer against NULL, we gain
-- information about that pointer on this branch.
--
-- Ignore floating point comparisons - only integer comparisons
-- are used for pointers.
addEdgeInformation :: NullabilityAnalysis -> EdgeCondition -> NullabilityAnalysis
addEdgeInformation n (TrueEdge cmp) = case valueContent cmp of
  ICmpInst ICmpEq v1 Value { valueContent = ConstantPointerNull } ->
    recordNullPtr v1 n
  ICmpInst ICmpEq Value { valueContent = ConstantPointerNull } v2 ->
    recordNullPtr v2 n
  ICmpInst ICmpNe v1 Value { valueContent = ConstantPointerNull } ->
    recordNotNullPtr v1 n
  ICmpInst ICmpNe Value { valueContent = ConstantPointerNull } v2 ->
    recordNotNullPtr v2 n
  _ -> n
addEdgeInformation n (FalseEdge cmp) = case valueContent cmp of
  ICmpInst ICmpEq v1 Value { valueContent = ConstantPointerNull } ->
    recordNotNullPtr v1 n
  ICmpInst ICmpEq Value { valueContent = ConstantPointerNull } v2 ->
    recordNotNullPtr v2 n
  ICmpInst ICmpNe v1 Value { valueContent = ConstantPointerNull } ->
    recordNullPtr v1 n
  ICmpInst ICmpNe Value { valueContent = ConstantPointerNull } v2 ->
    recordNullPtr v2 n
  _ -> n
addEdgeInformation n _ = n

-- | Record the given value as known-to-be-null in the analysis state.
recordNullPtr :: Value -> NullabilityAnalysis -> NullabilityAnalysis
recordNullPtr v na = na { nullPtrs = v `S.insert` nullPtrs na }

-- | Record the given value as known-to-be-not-null in the analysis state.
-- If the value @v@ also has information about a field that is not null,
-- record that too.
recordNotNullPtr :: Value -> NullabilityAnalysis -> NullabilityAnalysis
recordNotNullPtr v na = case fldDesc `debug` printf "    Not-null ptr: %s\n  FldDesc: %s\n" (show v) (show fldDesc) of
  Nothing -> na' -- This comparison doesn't involve a field load
  Just fld -> na' { notNullFields = M.insert v fld (notNullFields na') } -- This one does
  where
    na' = na { notNullPtrs = v `S.insert` notNullPtrs na }
    -- ^ We can always record the value we know is null.
    fldDesc = structFieldDescriptorFromLoad v


structFieldDescriptorFromLoad :: Value -> Maybe FieldDescriptor
structFieldDescriptorFromLoad Value { valueContent =
                                         LoadInst { loadAddress =
                                                       Value { valueContent =
                                                                  BitcastInst addr } } } =
  fieldAccessInfo addr
structFieldDescriptorFromLoad Value { valueContent =
                                         LoadInst { loadAddress = addr } } =
  fieldAccessInfo addr
structFieldDescriptorFromLoad _ = Nothing
