module Foreign.Inference.Nullability (
  -- * Types
  -- NullabilityAnalysis(notNullablePtrs, errorPtrs, notNullableFields),
  -- FieldDescriptor(..),
  -- -- * Constructor
  -- emptyNullabilityAnalysis
  ) where

import Algebra.Lattice
import Data.List ( foldl' )
import Data.LLVM.CFG
import Data.LLVM
import Data.LLVM.Analysis.Dataflow
import Data.Hashable
import Data.HashMap.Strict ( HashMap )
import Data.HashSet ( HashSet )
import qualified Data.HashSet as S
import qualified Data.HashMap.Strict as M

{-

-- | Uniquely names one field of a struct type.
data FieldDescriptor = FD !Type !Int
                     deriving (Show, Eq, Ord)

instance Hashable FieldDescriptor where
  hash (FD t i) = hash t `combine` i

data NullabilityAnalysis =
  NA { nullPtrs :: HashSet Value
       -- ^ The pointers that are known to be NULL
     , notNullPtrs :: HashSet Value
       -- ^ The pointers that are known to be non-NULL
     , nullFields :: HashMap Value FieldDescriptor
       -- ^ Fields that are known to be NULL
     , notNullFields :: HashMap Value FieldDescriptor
       -- ^ Fields that are known to be not NULL
     , notNullablePtrs :: HashSet Value
       -- ^ An aggregate field of all pointers known to be not-nullable
     , errorPtrs :: HashSet Value
       -- ^ An aggregate field of all erroneously dereferenced pointers
     , notNullableFields :: HashSet FieldDescriptor
       -- ^ An aggregate field of all non-nullable fields
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
                        } = gepStructField it0 Nothing ixs
  where
    -- The second (optional) Type parameter is the enclosing
    -- NamedType, if any.  This is only really useful for the base
    -- case if it is actually a struct with a name, and improves
    -- reporting.  This way, fields are reported in terms of their
    -- named type instead of the anonymous Struct type.  Other cases
    -- can ignore this parameter and just pass in Nothing.
    gepStructField :: Type -> Maybe Type -> [Value] -> Maybe FieldDescriptor
    -- Put this one first since we always want to step through a named
    -- type, regardless of its indices
    gepStructField nt@(TypeNamed _ it) _ indices = gepStructField it (Just nt) indices
    -- This is the case we care about - the last index in a GEP into a
    -- struct type.  This is the field that is not nullable.
    gepStructField st@(TypeStruct its _) mNamedType [Value { valueContent = ConstantInt ix }] =
      case length its > fromIntegral ix of
        True -> Just $ FD (maybe st id mNamedType) (fromIntegral ix)
        False -> error "GEP index greater than struct type list length"
    -- This could happen if the last index is not constant or the
    -- current "base" isn't a struct type.
    gepStructField _ _ [_] = Nothing
    -- Otherwise, step through the index for this type
    gepStructField (TypeArray _ it) _ (_:rest) = gepStructField it Nothing rest
    gepStructField (TypePointer it _) _ (_:rest) = gepStructField it Nothing rest
    -- We can only resolve constant ints - it is probably an error to
    -- have a non-constant here with a struct type anyway.
    gepStructField (TypeStruct its _) _ ((Value {valueContent = ConstantInt ix}):rest) =
      case length its > fromIntegral ix of
        True -> gepStructField (its !! fromIntegral ix) Nothing rest
        False -> error "GEP index greater than struct type list length"
    gepStructField _ _ _ = Nothing
fieldAccessInfo _ = Nothing

-- | This function is just a wrapper around 'fieldAccessInfo' to get
-- the information for a field access involved in a Load or Store.
-- This is used in the case that we know a field is being read from or
-- written to and we need to know which one.
--
-- This function transparently handles bitcasts.
addrFieldAccessInfo :: Value -> Maybe FieldDescriptor
addrFieldAccessInfo Value {
  valueContent =
     LoadInst {
       loadAddress =
          Value { valueContent = BitcastInst addr } } } =
  fieldAccessInfo addr
addrFieldAccessInfo Value {
  valueContent =
     StoreInst {
       storeAddress =
          Value { valueContent = BitcastInst addr } } } =
  fieldAccessInfo addr
addrFieldAccessInfo Value { valueContent = LoadInst { loadAddress = addr } } =
  fieldAccessInfo addr
addrFieldAccessInfo Value { valueContent = StoreInst { storeAddress = addr } } =
  fieldAccessInfo addr
addrFieldAccessInfo _ = Nothing

-- | If the input is a Load or Store of an address calculation (GEP),
-- return the base address.  This is the first pointer in a chain
-- being dereferenced.
addrFieldAccessBase :: Value -> Maybe Value
addrFieldAccessBase Value {
  valueContent =
     LoadInst {
       loadAddress =
          Value {
            valueContent =
               GetElementPtrInst {
                 getElementPtrValue = v
                 }}}} = Just v
addrFieldAccessBase Value {
  valueContent =
     StoreInst {
       storeAddress =
          Value {
            valueContent =
               GetElementPtrInst {
                 getElementPtrValue = v
                 }}}} = Just v
addrFieldAccessBase Value {
  valueContent =
     LoadInst {
       loadAddress =
          Value {
            valueContent =
               BitcastInst Value {
                 valueContent =
                    GetElementPtrInst {
                      getElementPtrValue = v
                      }}}}} = Just v
addrFieldAccessBase Value {
  valueContent =
     StoreInst {
       storeAddress =
          Value {
            valueContent =
               BitcastInst Value {
                 valueContent =
                    GetElementPtrInst {
                      getElementPtrValue = v
                      }}}}} = Just v
addrFieldAccessBase _ = Nothing

-- | If this is a successor of a null test, add a fact.  This probably
-- also needs to handle getElementPtr, though that really only
-- calculates addresses.  Really, this will have to consult the
-- results of an alias analysis.
transferFunc :: NullabilityAnalysis -> Value -> [CFGEdge] -> NullabilityAnalysis
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
addDerefInfo na rawPtr =
  case (S.member p (nullPtrs na),
        S.member p (notNullPtrs na),
        addrFieldAccessInfo p,
        M.lookup p (notNullFields na)
       ) of

    -- This is an unlikely case, but here we know that a pointer is
    -- NULL and we see that it is being dereferenced.
    (True, _, _, _) -> na { errorPtrs = p `S.insert` errorPtrs na }
    -- In this case, the value being dereferenced is a pointer that
    -- was a struct field (fi).  The lookup in notNullFields in this
    -- case *fails*, meaning that nothing is known about this field
    -- and that this is a non-nullable field.
    (_, False, Just fi, Nothing) ->
      let na' = na { notNullablePtrs = p `S.insert` notNullablePtrs na
                   , notNullableFields = fi `S.insert` notNullableFields na
                   }
      in case addrFieldAccessBase rawPtr of
        Nothing -> na'
        Just base -> na' { notNullablePtrs = base `S.insert` notNullablePtrs na' }

    -- Here we have just found a non-nullable pointer.
    (_, False, _, _) -> na { notNullablePtrs = p `S.insert` notNullablePtrs na }
    -- Otherwise it isn't interesting and we don't add any information
    _ -> na
  where
    p = case valueContent rawPtr of
      GetElementPtrInst { getElementPtrValue = ptrBase } -> ptrBase
      BitcastInst Value { valueContent = GetElementPtrInst { getElementPtrValue = ptrBase } } -> ptrBase
      _ -> rawPtr


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
addEdgeInformation :: NullabilityAnalysis -> CFGEdge -> NullabilityAnalysis
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
recordNotNullPtr v na = case fldDesc of
  Nothing -> na' -- This comparison doesn't involve a field load
  Just fld -> na' { notNullFields = M.insert v fld (notNullFields na') } -- This one does
  where
    na' = na { notNullPtrs = v `S.insert` notNullPtrs na }
    -- ^ We can always record the value we know is null.
    fldDesc = addrFieldAccessInfo v

-}