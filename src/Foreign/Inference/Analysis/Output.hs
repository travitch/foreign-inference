{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses #-}
{-# LANGUAGE ViewPatterns, TemplateHaskell #-}
-- | This analysis identifies output parameters.
--
-- Output parameters are those pointer parameters whose target memory
-- is never read from, only written to.  This implies that the value
-- at the target of the pointer at the time of a call is irrelevant.
-- Bindings can then automatically manage these parameters for
-- callers.
--
-- It is a dataflow analysis that classifies pointer parameters as
-- input, output, or both.  The initial value for each pointer
-- parameter is unused and the meet operator is point-wise least upper
-- bound (LUB).
--
-- Currently this analysis only deals with scalar types.  A very
-- useful extension would be to cover aggregate types.  An aggregate
-- is an output parameter if all of its fields are overwritten.
module Foreign.Inference.Analysis.Output (
  -- * Interface
  OutputSummary,
  identifyOutput,

  -- * Testing
  outputSummaryToTestFormat
  ) where

import Control.DeepSeq
import Data.HashSet ( HashSet )
import qualified Data.HashSet as HS
import Data.Lens.Common
import Data.Lens.Template
import Data.List ( groupBy )
import Data.Map ( Map )
import qualified Data.Map as M
import Data.Set ( Set )
import qualified Data.Set as S
import Debug.Trace.LocationTH

import LLVM.Analysis
import LLVM.Analysis.CFG
import LLVM.Analysis.CallGraphSCCTraversal
import LLVM.Analysis.Dataflow

import Foreign.Inference.AnalysisMonad
import Foreign.Inference.Diagnostics
import Foreign.Inference.Interface

data ArgumentDirection = ArgIn
                       | ArgOut
                       | ArgBoth
                       deriving (Eq, Ord)

instance Show ArgumentDirection where
  show ArgIn = "in"
  show ArgOut = "out"
  show ArgBoth = "both"

instance NFData ArgumentDirection

-- | Tracks the direction of each argument
type SummaryType = Map Argument (ArgumentDirection, [Witness])
-- | Tracks the direction of fields of pointer-to-struct arguments.
-- If all of the fields of a struct argument are ArgOut, the struct
-- argument is output.
type FieldSummaryType = Map (Argument, Int) (ArgumentDirection, [Witness])
data OutputSummary =
  OutputSummary { _outputSummary :: SummaryType
                , _outputFieldSummary :: FieldSummaryType
                , _outputDiagnostics :: Diagnostics
                }

$(makeLens ''OutputSummary)

data OutInfo = OI { _outputInfo :: !(Map Argument (ArgumentDirection, Set Witness))
                  , _outputFieldInfo :: !(Map (Argument, Int) (ArgumentDirection, Set Witness))
                  , aggregates :: !(HashSet Argument)
                  }
             deriving (Eq, Show)

$(makeLens ''OutInfo)

instance Eq OutputSummary where
  (OutputSummary s1 fs1 _) == (OutputSummary s2 fs2 _) =
    s1 == s2 && fs1 == fs2

instance Monoid OutputSummary where
  mempty = OutputSummary mempty mempty mempty
  mappend (OutputSummary s1 sf1 d1) (OutputSummary s2 sf2 d2) =
    OutputSummary (M.union s1 s2) (M.union sf1 sf2) (mappend d1 d2)

instance NFData OutputSummary where
  rnf o@(OutputSummary s sf d) =
    s `deepseq` sf `deepseq` d `deepseq` o `seq` ()

instance HasDiagnostics OutputSummary where
  diagnosticLens = outputDiagnostics

instance SummarizeModule OutputSummary where
  summarizeFunction _ _ = []
  summarizeArgument = summarizeOutArgument

summarizeOutArgument :: Argument -> OutputSummary -> [(ParamAnnotation, [Witness])]
summarizeOutArgument a (OutputSummary s sf _) =
  case argumentFieldCount a of
    Nothing ->
      case M.lookup a s of
        Nothing -> []
        Just (ArgIn, _) -> []
        Just (ArgOut, ws) -> [(PAOut, ws)]
        Just (ArgBoth, ws) -> [(PAInOut, ws)]
    Just flds ->
      let argFieldDirs = filter (matchesArg a) $ M.toList sf
      in case length argFieldDirs == flds && all isOutField argFieldDirs of
        False -> []
        True -> [(PAOut, combineWitnesses argFieldDirs)]

matchesArg :: Argument -> ((Argument, a), b) -> Bool
matchesArg a ((ma, _), _) = ma == a

isOutField :: (a, (ArgumentDirection, b)) -> Bool
isOutField (_, (ArgOut, _)) = True
isOutField _ = False

combineWitnesses :: [(a, (b, [Witness]))] -> [Witness]
combineWitnesses = concatMap (snd . snd)


-- | If the argument is a pointer to a struct, return the number of
-- fields in the struct.  Otherwise, return Nothing.
argumentFieldCount :: Argument -> Maybe Int
argumentFieldCount a =
  case argumentType a of
    TypePointer (TypeStruct _ flds _) _ -> Just (length flds)
    _ -> Nothing

data OutData = OD { moduleSummary :: OutputSummary
                  , dependencySummary :: DependencySummary
                  }

-- | Note that array parameters are not out parameters, so we rely on
-- the Array analysis to let us filter those parameters out of our
-- results.
identifyOutput :: (FuncLike funcLike, HasCFG funcLike, HasFunction funcLike)
                  => DependencySummary
                  -> Lens compositeSummary OutputSummary
                  -> ComposableAnalysis compositeSummary funcLike
identifyOutput ds lns =
  composableAnalysisM runner outAnalysis lns
  where
    runner a = runAnalysis a constData ()
    constData = OD mempty ds


instance MeetSemiLattice OutInfo where
  meet = meetOutInfo

instance MeetSemiLattice ArgumentDirection where
  meet ArgIn ArgIn = ArgIn
  meet ArgOut ArgOut = ArgOut
  meet ArgIn ArgOut = ArgBoth
  meet ArgOut ArgIn = ArgBoth
  meet ArgBoth _ = ArgBoth
  meet _ ArgBoth = ArgBoth

instance BoundedMeetSemiLattice OutInfo where
  top = OI mempty mempty mempty

meetOutInfo :: OutInfo -> OutInfo -> OutInfo
meetOutInfo (OI m1 mf1 s1) (OI m2 mf2 s2) =
  OI (M.unionWith meetWithWitness m1 m2) (M.unionWith meetWithWitness mf1 mf2) (s1 `HS.union` s2)
  where
    meetWithWitness (v1, w1) (v2, w2) = (meet v1 v2, S.union w1 w2)

instance DataflowAnalysis Analysis OutInfo where
  transfer = outTransfer

type Analysis = AnalysisMonad OutData ()

outAnalysis :: (FuncLike funcLike, HasFunction funcLike, HasCFG funcLike)
               => funcLike -> OutputSummary -> Analysis OutputSummary
outAnalysis funcLike s = do
  let envMod e = e { moduleSummary = s }
  funcInfo <- local envMod (forwardDataflow top funcLike)
  let exitInfo = map (dataflowResult funcInfo) (functionExitInstructions f)
      OI exitInfo' fexitInfo' aggArgs = meets exitInfo
      exitInfo'' = M.filterWithKey (\k _ -> not (HS.member k aggArgs)) exitInfo'
      exitInfo''' = M.map (\(a, ws) -> (a, S.toList ws)) exitInfo''
      fexitInfo'' = M.map (\(a, ws) -> (a, S.toList ws)) fexitInfo'
  -- Merge the local information we just computed with the global
  -- summary.  Prefer the locally computed info if there are
  -- collisions (could arise while processing SCCs).
  return $! (outputSummary ^!%= M.union exitInfo''') $ (outputFieldSummary ^!%= M.union fexitInfo'') s
  where
    f = getFunction funcLike

-- | This transfer function only needs to be concerned with Load and
-- Store instructions (for now).  Loads add in an ArgIn value. Stores
-- add an ArgOut.
--
-- Note, we don't use valueContent' to strip bitcasts here since
-- accesses to bitfields use lots of interesting bitcasts and give us
-- false positives.
outTransfer :: OutInfo -> Instruction -> Analysis OutInfo
outTransfer info i =
  case i of
    LoadInst { loadAddress = (valueContent -> ArgumentC ptr) } ->
      return $! merge outputInfo i ptr ArgIn info
    StoreInst { storeAddress = (valueContent -> ArgumentC ptr) } ->
      return $! merge outputInfo i ptr ArgOut info
    AtomicRMWInst { atomicRMWPointer = (valueContent -> ArgumentC ptr) } ->
      return $! merge outputInfo i ptr ArgBoth info
    AtomicCmpXchgInst { atomicCmpXchgPointer = (valueContent -> ArgumentC ptr) } ->
      return $! merge outputInfo i ptr ArgBoth info

    LoadInst { loadAddress = (valueContent -> InstructionC
      GetElementPtrInst { getElementPtrValue = (valueContent -> ArgumentC ptr)
                        , getElementPtrIndices = [ (valueContent -> ConstantC (ConstantInt _ _ 0))
                                                 , (valueContent -> ConstantC (ConstantInt _ _ fldNo))
                                                 ]
                        })} ->
      return $! merge outputFieldInfo i (ptr, (fromIntegral fldNo)) ArgIn info
    StoreInst { storeAddress = (valueContent -> InstructionC
      GetElementPtrInst { getElementPtrValue = (valueContent -> ArgumentC ptr)
                        , getElementPtrIndices = [ (valueContent -> ConstantC (ConstantInt _ _ 0))
                                                 , (valueContent -> ConstantC (ConstantInt _ _ fldNo))
                                                 ]
                        })} ->
      return $! merge outputFieldInfo i (ptr, (fromIntegral fldNo)) ArgOut info
    AtomicRMWInst { atomicRMWPointer = (valueContent -> InstructionC
      GetElementPtrInst { getElementPtrValue = (valueContent -> ArgumentC ptr)
                        , getElementPtrIndices = [ (valueContent -> ConstantC (ConstantInt _ _ 0))
                                                 , (valueContent -> ConstantC (ConstantInt _ _ fldNo))
                                                 ]
                        })} ->
      return $! merge outputFieldInfo i (ptr, (fromIntegral fldNo)) ArgBoth info
    AtomicCmpXchgInst { atomicCmpXchgPointer = (valueContent -> InstructionC
      GetElementPtrInst { getElementPtrValue = (valueContent -> ArgumentC ptr)
                        , getElementPtrIndices = [ (valueContent -> ConstantC (ConstantInt _ _ 0))
                                                 , (valueContent -> ConstantC (ConstantInt _ _ fldNo))
                                                 ]
                        })} ->
      return $! merge outputFieldInfo i (ptr, (fromIntegral fldNo)) ArgBoth info

    -- We don't want to treat any aggregates as output parameters yet.
    -- Record all arguments used as aggregates and filter them out at
    -- the end of the analysis.
    --
    -- Later, we want to expand the definition of output parameters to
    -- cover structs where all fields are initialized.
    GetElementPtrInst { getElementPtrValue = (valueContent' -> ArgumentC ptr) } ->
      return $! info { aggregates = HS.insert ptr (aggregates info) }

    CallInst { callFunction = f, callArguments = args } ->
      callTransfer info i f (map fst args)
    InvokeInst { invokeFunction = f, invokeArguments = args }->
      callTransfer info i f (map fst args)

    _ -> return info

callTransfer :: OutInfo -> Instruction -> Value -> [Value] -> Analysis OutInfo
callTransfer info i f args = do
  let indexedArgs = zip [0..] args
  modSumm <- asks moduleSummary
  depSumm <- asks dependencySummary

  foldM (checkArg depSumm modSumm) info indexedArgs
  where
    checkArg ds ms acc (ix, arg) =
      case valueContent' arg of
        ArgumentC a ->
          case lookupArgumentSummary ds ms f ix of
            Nothing -> do
              let errMsg = "No summary for " ++ show (valueName f)
              emitWarning Nothing "OutputAnalysis" errMsg
              return acc
            Just attrs ->
              case PAOut `elem` attrs of
                True -> return $! merge outputInfo i a ArgOut acc
                False -> return $! merge outputInfo i a ArgIn acc
        _ -> return acc

merge :: (Ord k)
         => Lens info (Map k (ArgumentDirection, Set Witness))
         -> Instruction -> k -> ArgumentDirection -> info -> info
merge lns i arg ArgBoth info =
  let ws = S.singleton (Witness i (show ArgBoth))
  in (lns ^!%= M.insert arg (ArgBoth, ws)) info
merge lns i arg newVal info =
  case M.lookup arg (info ^. lns) of
    Nothing ->
      let ws = S.singleton (Witness i (show newVal))
      in (lns ^!%= M.insert arg (newVal, ws)) info
    Just (ArgBoth, _) -> info
    Just (ArgOut, _) -> info
    Just (ArgIn, ws) ->
      case newVal of
        ArgOut ->
          let nw = Witness i (show ArgBoth)
          in (lns ^!%= M.insert arg (ArgBoth, S.insert nw ws)) info
        ArgIn -> info
        ArgBoth -> $failure "Infeasible path"

removeArrayPtr :: Argument -> OutInfo -> OutInfo
removeArrayPtr a (OI oi foi ag) = OI (M.delete a oi) foi ag

-- Testing

-- | Convert an Output summary to a format more suitable for
-- testing
outputSummaryToTestFormat :: OutputSummary -> Map String (Set (String, ParamAnnotation))
outputSummaryToTestFormat (OutputSummary s sf _) =
  M.union scalarParams aggregateParams
  where
    scalarParams = foldr collectArgs mempty (M.toList s)

    aggList = groupBy sameArg (M.toList sf)
    aggListByArg = map flattenArg aggList
    aggregateParams = foldr collectAggArgs mempty aggListByArg

    sameArg ((a, _), _) ((b, _), _) = a == b
    flattenArg :: [((Argument, Int), (ArgumentDirection, [Witness]))]
                  -> (Argument, [(Int, ArgumentDirection)])
    flattenArg allFields@(((a, _), _) : _) =
      (a, map flatten' allFields)
    flatten' ((_, ix), (dir, _)) = (ix, dir)

    dirToAnnot d =
      case d of
        ArgIn -> Nothing
        ArgOut -> Just PAOut
        ArgBoth -> Just PAInOut

    isOut (_, argDir) = argDir == ArgOut

    collectAggArgs (arg, fieldDirections) acc =
      let func = argumentFunction arg
          funcName = show (functionName func)
          argName = show (argumentName arg)
      in case argumentFieldCount arg of
        Nothing -> error ("Expected aggregate type in field direction summary " ++ show arg)
        Just fldCnt ->
          case length fieldDirections == fldCnt && all isOut fieldDirections of
            False -> acc
            True ->
              let nv = S.singleton (argName, PAOut)
              in M.insertWith' S.union funcName nv acc

    collectArgs (arg, (dir, _)) acc =
      let func = argumentFunction arg
          funcName = show (functionName func)
          argName = show (argumentName arg)
      in case dirToAnnot dir of
        Nothing -> acc
        Just annot ->
          let nv = S.singleton (argName, annot)
          in M.insertWith' S.union funcName nv acc
