{-# LANGUAGE ViewPatterns #-}
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

import Data.List ( elemIndex, foldl' )
import Data.List.Ordered ( union )
import Data.Map ( Map )
import qualified Data.Map as M
import Data.Monoid

import LLVM.Analysis
import LLVM.Analysis.AccessPath

-- import Text.Printf
-- import Debug.Trace
-- debug = flip trace

-- Also, allow paths in finalizers to include exit-like functions.

data SingleInitializerSummary =
  SIS { abstractPathInitializers :: !(Map AbstractAccessPath [Value])
      , concreteValueInitializers :: !(Map GlobalVariable [Value])
      , argumentInitializers :: !(Map (Function, Int) [Value])
      , fieldArgDependencies :: !(Map AbstractAccessPath [(Function, Int)])
      , globalArgDependencies :: !(Map GlobalVariable [(Function, Int)])
      }
  deriving (Eq)

instance Monoid SingleInitializerSummary where
  mempty = SIS mempty mempty mempty mempty mempty
  mappend (SIS a1 c1 arg1 f1 g1) (SIS a2 c2 arg2 f2 g2) =
    SIS (a1 `mappend` a2) (c1 `mappend` c2) (arg1 `mappend` arg2) (f1 `mappend` f2) (g1 `mappend` g2)

singleInitializer :: SingleInitializerSummary -> Value -> [Value]
singleInitializer s v =
  case valueContent' v of
    InstructionC i -> maybe [] id $ do
      accPath <- accessPath i
      let absPath = abstractAccessPath accPath
      case valueContent' (accessPathBaseValue accPath) of
        GlobalVariableC gv@GlobalVariable { globalVariableInitializer = Just initVal } ->
          case followAccessPath absPath initVal of
            Nothing -> return $! globalVarLookup s gv
            accPathVal -> fmap return accPathVal
        _ -> return $! absPathLookup s absPath
    _ -> []

absPathLookup :: SingleInitializerSummary -> AbstractAccessPath -> [Value]
absPathLookup s absPath = storeInits `union` argInits
  where
    storeInits = M.findWithDefault [] absPath (abstractPathInitializers s)
    argDeps = M.findWithDefault [] absPath (fieldArgDependencies s)
    argInits = concatMap (\x -> M.findWithDefault [] x (argumentInitializers s)) argDeps

globalVarLookup :: SingleInitializerSummary -> GlobalVariable -> [Value]
globalVarLookup s gv = concreteInits `union` argInits
  where
    concreteInits = M.findWithDefault [] gv (concreteValueInitializers s)
    argDeps = M.findWithDefault [] gv (globalArgDependencies s)
    argInits = concatMap (\x -> M.findWithDefault [] x (argumentInitializers s)) argDeps

identifySingleInitializers :: Module -> SingleInitializerSummary
identifySingleInitializers m =
  foldl' (flip recordInitializers) s0 allInsts
  where
    s0 = mempty { concreteValueInitializers = M.fromList globalsWithInits }
    allBlocks = concatMap functionBody $ moduleDefinedFunctions m
    allInsts = concatMap basicBlockInstructions allBlocks
    globalsWithInits = foldr extractGlobalsWithInits [] (moduleGlobalVariables m)

extractGlobalsWithInits :: GlobalVariable
                           -> [(GlobalVariable, [Value])]
                           -> [(GlobalVariable, [Value])]
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
        ArgumentC a ->
          let f = argumentFunction a
              Just ix = elemIndex a (functionParameters f)
          in recordArgInitializer i f ix sa s
        _ -> s
    CallInst { callFunction = (valueContent' -> FunctionC f)
             , callArguments = args
             } ->
      let ixArgs = zip [0..] $ map fst args
      in foldl' (recordArgFuncInit f) s ixArgs
    InvokeInst { invokeFunction = (valueContent' -> FunctionC f)
               , invokeArguments = args
               } ->
      let ixArgs = zip [0..] $ map fst args
      in foldl' (recordArgFuncInit f) s ixArgs
    _ -> s

-- | If an actual argument has a Function (or ExternalFunction) as its
-- value, record that as a value as associated with the ix'th argument
-- of the callee.
recordArgFuncInit :: Function
                     -> SingleInitializerSummary
                     -> (Int, Value)
                     -> SingleInitializerSummary
recordArgFuncInit f s (ix, arg) =
  case valueContent' arg of
    FunctionC _ ->
      s { argumentInitializers =
             M.insertWith union (f, ix) [arg] (argumentInitializers s)
        }
    ExternalFunctionC _ ->
      s { argumentInitializers =
             M.insertWith union (f, ix) [arg] (argumentInitializers s)
        }
    _ -> s

recordArgInitializer :: Instruction
                        -> Function
                        -> Int
                        -> Value
                        -> SingleInitializerSummary
                        -> SingleInitializerSummary
recordArgInitializer i f ix sa s =
  case valueContent' sa of
    GlobalVariableC gv ->
      s { globalArgDependencies =
             M.insertWith' union gv [(f, ix)] (globalArgDependencies s)
        }
    _ ->
      case accessPath i of
        Nothing -> s
        Just accPath ->
          let absPath = abstractAccessPath accPath
          in s { fieldArgDependencies =
                    M.insertWith' union absPath [(f, ix)] (fieldArgDependencies s)
               }

-- | Initializers here (sv) are only functions (external or otherwise)
maybeRecordInitializer :: Instruction -> Value -> Value
                          -> SingleInitializerSummary
                          -> SingleInitializerSummary
maybeRecordInitializer i sv sa s =
  case valueContent' sa of
    GlobalVariableC gv ->
      s { concreteValueInitializers =
             M.insertWith' union gv [sv] (concreteValueInitializers s)
        }
    _ ->
      case accessPath i of
        Nothing -> s
        Just accPath ->
          let absPath = abstractAccessPath accPath
          in s { abstractPathInitializers =
                    M.insertWith' union absPath [sv] (abstractPathInitializers s)
               }
