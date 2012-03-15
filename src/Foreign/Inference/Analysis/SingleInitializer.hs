-- | FIXME: Currently there is an exception allowing us to identify
-- finalizers that are called through function pointers if the
-- function pointer is global and has an initializer.
--
-- This needs to be generalized to cover things that are initialized
-- once in the library code with a finalizer.  This will be a lower-level
-- analysis that answers the query:
--
-- > initializedOnce :: Value -> Maybe Value
--
-- where the returned value is the single initializer that was sourced
-- within the library.  This can be the current simple analysis for
-- globals with initializers.  Others will be analyzed in terms of
-- access paths (e.g., Field X of Type Y is initialized once with
-- value Z).
--
-- Linear scan for all stores, recording their access path.  Also look
-- at all globals (globals can be treated separately).  If an access
-- path gets more than one entry, stop tracking it.  Only record
-- stores where the value is some global entity.
--
-- Run this analysis after or before constructing the call graph and
-- initialize the whole-program summary with it.  It doesn't need to
-- be computed bottom up as part of the call graph traversal.
module Foreign.Inference.Analysis.SingleInitializer (
  SingleInitializerSummary,
  identifySingleInitializers,
  singleInitializer
  ) where

import Data.List ( foldl' )
import Data.List.Ordered ( insertSet )
import Data.Map ( Map )
import qualified Data.Map as M
import Data.Monoid

import LLVM.Analysis
import LLVM.Analysis.AccessPath

data SingleInitializerSummary =
  SIS { abstractPathInitializers :: !(Map AbstractAccessPath [Value])
      , concreteValueInitializers :: !(Map GlobalVariable [Value])
      }
  deriving (Eq)

instance Monoid SingleInitializerSummary where
  mempty = SIS mempty mempty
  mappend (SIS a1 c1) (SIS a2 c2) =
    SIS (a1 `mappend` a2) (c1 `mappend` c2)

singleInitializer :: SingleInitializerSummary -> Value -> [Value]
singleInitializer s v =
  case valueContent' v of
    InstructionC i -> maybe [] id $ do
      accPath <- accessPath i
      let absPath = abstractAccessPath accPath
      case valueContent' (accessPathBaseValue accPath) of
        GlobalVariableC gv@GlobalVariable { globalVariableInitializer = Just initVal } ->
          case followAccessPath absPath initVal of
            Nothing -> M.lookup gv (concreteValueInitializers s)
            accPathVal -> fmap return accPathVal
        _ -> M.lookup absPath (abstractPathInitializers s)
    _ -> []

identifySingleInitializers :: Module -> SingleInitializerSummary
identifySingleInitializers m =
  foldl' (flip recordInitializers) s0 allInsts
  where
    s0 = mempty { concreteValueInitializers = M.fromList globalsWithInits }
    allBlocks = concatMap functionBody $ moduleDefinedFunctions m
    allInsts = concatMap basicBlockInstructions allBlocks
    globalsWithInits = foldr extractGlobalsWithInits [] (moduleGlobalVariables m)

extractGlobalsWithInits gv acc =
  case globalVariableInitializer gv of
    Nothing -> acc
    Just i -> (gv, [i]) : acc

recordInitializers :: Instruction -> SingleInitializerSummary -> SingleInitializerSummary
recordInitializers i s =
  case i of
    StoreInst { storeValue = sv, storeAddress = sa } ->
      case valueContent' sv of
        FunctionC _ -> maybeRecordInitializer i sv sa s
        ExternalFunctionC _ -> maybeRecordInitializer i sv sa s
        _ -> s
    _ -> s

-- | Initializers here (sv) are only functions (external or otherwise)
maybeRecordInitializer :: Instruction -> Value -> Value
                          -> SingleInitializerSummary
                          -> SingleInitializerSummary
maybeRecordInitializer i sv sa s =
  case valueContent' sa of
    GlobalVariableC gv ->
      case M.lookup gv (concreteValueInitializers s) of
        Nothing ->
          s { concreteValueInitializers =
                 M.insert gv [sv] (concreteValueInitializers s)
            }
        Just current ->
          s { concreteValueInitializers =
                 M.insert gv (insertSet sv current) (concreteValueInitializers s)
            }
    _ ->
      case accessPath i of
        Nothing -> s
        Just accPath ->
          let absPath = abstractAccessPath accPath
          in case M.lookup absPath (abstractPathInitializers s) of
            Nothing ->
              s { abstractPathInitializers =
                     M.insert absPath [sv] (abstractPathInitializers s)
                }
            Just current ->
              s { abstractPathInitializers =
                     M.insert absPath (insertSet sv current) (abstractPathInitializers s)
                }
