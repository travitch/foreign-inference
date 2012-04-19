{-# LANGUAGE OverloadedStrings, ExistentialQuantification, DeriveDataTypeable #-}
{-# LANGUAGE TemplateHaskell, StandaloneDeriving, ViewPatterns #-}
-- | This module defines an external representation of library
-- interfaces.  Individual libraries are represented by the
-- 'LibraryInterface'.  The analysis reads these in and writes these
-- out.
--
-- During the analysis, the dependencies of the current library are
-- represented using the 'DependencySummary', which is composed of
-- several 'LibraryInterface's.
--
-- Note that this module does not currently handle by-value structs
-- properly.  The various LLVM frontends lower these according to the
-- target ABI and it is a bit difficult to map the result exactly back
-- to how it appeared in the source.  This will have to be done with
-- some metadata.
--
-- NOTE! A possible name for the project: Inferred Interface Glue - IIGlue
module Foreign.Inference.Interface (
  -- * Classes
  SummarizeModule(..),
  ModuleSummary(..),
  -- * Types
  Witness(..),
  DependencySummary(libraryAnnotations),
  LibraryInterface(..),
  LibraryAnnotations,
  ForeignFunction(..),
  Parameter(..),
  CEnum(..),
  CType(..),
  Linkage(..),
  ParamAnnotation(..),
  FuncAnnotation(..),
  StdLib(..),
  -- * Functions
  lookupArgumentSummary,
  lookupFunctionSummary,
  loadDependencies,
  loadDependencies',
  moduleToLibraryInterface,
  saveInterface,
  saveModule,
  readLibraryInterface,
  addLibraryAnnotations,
  loadAnnotations,
  -- *
  userFunctionAnnotations,
  userParameterAnnotations
  ) where

import Prelude hiding ( catch )

import Control.DeepSeq
import Control.Exception
import Data.Aeson
import Data.ByteString.Char8 ( ByteString )
import qualified Data.ByteString.Char8 as SBS
import qualified Data.ByteString.Lazy as LBS
import Data.Data
import Data.FileEmbed
import Data.HashMap.Strict ( HashMap )
import qualified Data.HashMap.Strict as M
import Data.Map ( Map )
import qualified Data.Map as Map
import Data.IntMap ( IntMap )
import qualified Data.IntMap as IM
import Data.Maybe ( mapMaybe )
import Data.Monoid
import Data.Set ( Set )
import qualified Data.Set as S
import Data.List ( foldl' )
import Debug.Trace.LocationTH
import System.FilePath
import System.IO.Error hiding ( catch )

import LLVM.Analysis

import Foreign.Inference.Interface.Metadata
import Foreign.Inference.Interface.Types

-- import Debug.Trace
-- debug = flip trace

-- | The extension used for all summaries
summaryExtension :: String
summaryExtension = "json"

libc :: SBS.ByteString
libc = $(embedFile "stdlibs/c.json")
libm :: SBS.ByteString
libm = $(embedFile "stdlibs/m.json")
llvmIntrinsics :: SBS.ByteString
llvmIntrinsics = $(embedFile "stdlibs/llvm.json")

data InterfaceException = DependencyMissing FilePath
                        | DependencyDecodeError FilePath
                        deriving (Show, Typeable)
instance Exception InterfaceException


type LibraryAnnotations = Map ByteString ([FuncAnnotation], IntMap [ParamAnnotation])
type DepMap = HashMap ByteString ForeignFunction

-- | A summary of all of the functions that are dependencies of the
-- current library.
data DependencySummary = DS { depSummary :: DepMap
                            , libraryAnnotations :: LibraryAnnotations
                            }
                       deriving (Show)

addLibraryAnnotations :: DependencySummary -> LibraryAnnotations -> DependencySummary
addLibraryAnnotations ds as = ds { libraryAnnotations = libraryAnnotations ds `mappend` as }

-- | The standard library summaries that can be automatically loaded
-- by 'loadDependencies''.
data StdLib = CStdLib
            | CxxStdLib
            | LLVMLib
            deriving (Show)

-- | A witness is an instruction and a (short) free-form string
-- describing what was witnessed on that line.
--
-- The file name is not included because the file is identified by the
-- enclosing function of the Argument.
--
-- WARNING: Don't put anything javascript-unsafe in the String.  This
-- could be enforced but doesn't seem worth the effort right now.
data Witness = Witness !Instruction String
             deriving (Eq, Ord, Show)

instance NFData Witness where
  rnf w@(Witness _ s) = s `deepseq` w `seq` ()

-- | An existential wrapper around types implementing
-- 'SummarizeModule' to allow heterogenous lists of analysis results.
data ModuleSummary = forall a . (SummarizeModule a) => ModuleSummary a

-- | An interface for analyses to implement in order to annotate
-- constructs in 'Module's.
class SummarizeModule s where
  summarizeArgument :: Argument -> s -> [(ParamAnnotation, [Witness])]
  summarizeFunction :: Function -> s -> [FuncAnnotation]

instance SummarizeModule ModuleSummary where
  summarizeArgument a (ModuleSummary s) = summarizeArgument a s
  summarizeFunction f (ModuleSummary s) = summarizeFunction f s

-- | Persist a 'LibraryInterface' to disk in the given @summaryDir@.
-- It uses the name specified in the 'LibraryInterface' to choose the
-- filename.
--
-- > saveInterface summaryDir iface
saveInterface :: FilePath -> LibraryInterface -> IO ()
saveInterface summaryDir i = do
  let bs = encode i
      path = summaryDir </> libraryName i <.> summaryExtension
  LBS.writeFile path bs

-- | A shortcut to convert a 'Module' into a 'LibraryInterface' and
-- then persist it as in 'saveInterface'.
saveModule :: FilePath -> String -> [String] -> Module -> [ModuleSummary] -> DependencySummary -> IO ()
saveModule summaryDir name deps m summaries ds = do
  let i = moduleToLibraryInterface m name deps summaries (libraryAnnotations ds)
  saveInterface summaryDir i

-- | Load annotations supplied by the user
loadAnnotations :: FilePath -> IO LibraryAnnotations
loadAnnotations p = do
  c <- LBS.readFile p
  case decode' c of
    Nothing ->
      let ex = mkIOError doesNotExistErrorType "loadAnnotations" Nothing (Just p)
      in ioError ex
    Just li -> return li

-- | A call
--
-- > loadDependencies summaryDir deps
--
-- Loads all of the 'LibraryInterface's transitively required by
-- @deps@ from any directory in @summaryDirs@.  The @summaryDirs@ are
-- searched in order.  Will throw an exception if a required
-- dependency is not found.
--
-- This variant will automatically include the C standard library (and
-- eventually the C++ standard library).
loadDependencies :: [FilePath] -> [String] -> IO DependencySummary
loadDependencies = loadDependencies' [CStdLib, LLVMLib]


-- | The same as 'loadDependencies', except it gives the option of not
-- automatically loading standard library summaries.
loadDependencies' :: [StdLib] -> [FilePath] -> [String] -> IO DependencySummary
loadDependencies' includeStd summaryDirs deps = do
  let baseDeps = foldl' addStdlibDeps M.empty includeStd
  m <- loadTransDeps summaryDirs deps S.empty baseDeps
  return (DS m mempty)
  where
    addStdlibDeps m CStdLib =
      let lc = decodeInterface libc
          lm = decodeInterface libm
          fs = libraryFunctions lc ++ libraryFunctions lm
      in foldl' mergeFunction m fs
    addStdlibDeps m LLVMLib =
      let ll = decodeInterface llvmIntrinsics
      in foldl' mergeFunction m (libraryFunctions ll)


-- | Load all of the dependencies requested (transitively).  This just
-- iterates loading interfaces and recording all of the new
-- dependencies until there are no more.
--
-- Note that this function does not need to load types from library
-- descriptions because LLVM will have definitions for any public
-- struct types already.  The type descriptions are only useful for
-- binding generation.
loadTransDeps :: [FilePath] -> [String] -> Set String -> DepMap -> IO DepMap
loadTransDeps summaryDirs deps loadedDeps m = do
  let unmetDeps = filter (`S.notMember` loadedDeps) deps
      paths = map (<.> summaryExtension) unmetDeps
  case unmetDeps of
    [] -> return m
    _ -> do
      newInterfaces <- mapM (parseInterface summaryDirs) paths
      let newDeps = concatMap libraryDependencies newInterfaces
          newFuncs = concatMap libraryFunctions newInterfaces
          loadedDeps' = loadedDeps `S.union` S.fromList unmetDeps
          m' = foldl' mergeFunction m newFuncs
      loadTransDeps summaryDirs newDeps loadedDeps' m'

-- | Try to "link" function summaries into the current
-- 'DependencySummary'.  This makes a best effort to deal with weak
-- symbols.  Weak symbols get overridden arbitrarily.  If two non-weak
-- symbols with the same name are encountered, this function just
-- raises an error.
mergeFunction :: DepMap -> ForeignFunction -> DepMap
mergeFunction m f = case M.lookup fn m of
  Nothing -> M.insert fn f m
  Just (ForeignFunction { foreignFunctionLinkage = LinkWeak }) -> M.insert fn f m
  Just f' -> case foreignFunctionLinkage f of
    LinkWeak -> m
    LinkDefault ->
      case f == f' of
        True -> m
        False ->
          $failure ("Functions with overlapping linkage: " ++ show f ++ " and " ++ show f')
  where
    fn = SBS.pack $ foreignFunctionName f

-- | This is a low-level helper to load a LibraryInterface from a
-- location on disk.
readLibraryInterface :: FilePath -> IO LibraryInterface
readLibraryInterface p = do
  c <- LBS.readFile p
  case decode' c of
    Nothing ->
      let ex = mkIOError doesNotExistErrorType "readLibraryInterface" Nothing (Just p)
      in ioError ex
    Just li -> return li

-- | This is a high-level interface that searches for a named library
-- in several locations (@summaryDirs@).
--
-- Try to load the named file from all possible summary repository
-- dirs.
parseInterface :: [FilePath] -> FilePath -> IO LibraryInterface
parseInterface summaryDirs p = do
  c <- loadFromSources summaryDirs p
  let mval = decode' c
  case mval of
    Nothing -> throw (DependencyDecodeError p)
    Just li -> return li

decodeInterface :: SBS.ByteString -> LibraryInterface
decodeInterface bs =
  case decode' (LBS.fromChunks [bs]) of
    Nothing -> throw (DependencyDecodeError "builtin")
    Just li -> li

loadFromSources :: [FilePath] -> FilePath -> IO LBS.ByteString
loadFromSources (src:rest) p = catch (LBS.readFile fname) handleMissingSrc
  where
    fname = src </> p
    handleMissingSrc :: IOException -> IO LBS.ByteString
    handleMissingSrc _ = loadFromSources rest p
loadFromSources [] p = throw (DependencyMissing p)

-- | Convert a Module to a LibraryInterface using the information in
-- the provided 'ModuleSummary's.
moduleToLibraryInterface :: Module   -- ^ Module to summarize
                            -> String   -- ^ Module name
                            -> [String] -- ^ Module dependencies
                            -> [ModuleSummary] -- ^ Summary information from analyses
                            -> LibraryAnnotations
                            -> LibraryInterface
moduleToLibraryInterface m name deps summaries annots =
  LibraryInterface { libraryFunctions = funcs
                   , libraryTypes = moduleInterfaceStructTypes m
                   , libraryName = name
                   , libraryDependencies = deps
                   , libraryEnums = moduleInterfaceEnumerations m
                   }
  where
    funcs = mapMaybe (functionToExternal summaries annots) (moduleDefinedFunctions m)


-- | Summarize a single function.  Functions with types in their
-- signatures that have certain exotic types are not supported in
-- interfaces.
functionToExternal :: [ModuleSummary] -> LibraryAnnotations -> Function -> Maybe ForeignFunction
functionToExternal summaries annots f =
  case vis of
    VisibilityHidden -> Nothing
    _ -> do
      lnk <- toLinkage (functionLinkage f)
      fretty <- typeToCType (functionReturnMetaUnsigned f) fretType
      let indexedArgs = zip [0..] (functionParameters f)
      params <- mapM (paramToExternal summaries annots) indexedArgs
      return ForeignFunction { foreignFunctionName = SBS.unpack $ identifierContent (functionName f)
                             , foreignFunctionLinkage =
                                  if vis == VisibilityProtected then LinkWeak else lnk
                             , foreignFunctionReturnType = fretty
                             , foreignFunctionParameters = params
                             , foreignFunctionAnnotations = fannots
                             }
  where
    vis = functionVisibility f
    fannots = concat [ userFunctionAnnotations annots f
                    , concatMap (summarizeFunction f) summaries
                    ]
    fretType = case functionType f of
      TypeFunction rt _ _ -> rt
      t -> t

paramToExternal :: [ModuleSummary] -> LibraryAnnotations -> (Int, Argument) -> Maybe Parameter
paramToExternal summaries annots (ix, arg) = do
  ptype <- typeToCType (paramMetaUnsigned arg) (argumentType arg)
  return Parameter { parameterType = ptype
                   , parameterName = SBS.unpack (identifierContent (argumentName arg))
                   , parameterAnnotations =
                     concat [ userParameterAnnotations annots f ix
                              -- The map fst here drops witness information -
                              -- we don't need to expose that in summaries.
                            , concatMap (map fst . summarizeArgument arg) summaries
                            ]
                   }
  where
    f = argumentFunction arg

isVarArg :: ExternalFunction -> Bool
isVarArg ef = isVa
  where
    (TypeFunction _ _ isVa) = externalFunctionType ef

userFunctionAnnotations :: LibraryAnnotations -> Function -> [FuncAnnotation]
userFunctionAnnotations allAnnots f =
  case fannots of
    Nothing -> []
    Just (fas, _) -> fas
  where
    fname = identifierContent $ functionName f
    fannots = Map.lookup fname allAnnots

userParameterAnnotations :: LibraryAnnotations -> Function -> Int -> [ParamAnnotation]
userParameterAnnotations allAnnots f ix =
  case fannots of
    Nothing -> []
    Just (_, pmap) -> IM.findWithDefault [] ix pmap

  where
    fname = identifierContent $ functionName f
    fannots = Map.lookup fname allAnnots


lookupFunctionSummary :: (IsValue v, SummarizeModule s)
                         => DependencySummary
                         -> s
                         -> v
                         -> Maybe [FuncAnnotation]
lookupFunctionSummary ds ms val =
  case valueContent' val of
    FunctionC f ->
      let fannots = userFunctionAnnotations (libraryAnnotations ds) f
      in return $! fannots ++ summarizeFunction f ms
    ExternalFunctionC ef -> do
      let fname = identifierContent $ externalFunctionName ef
          summ = depSummary ds
      fsum <- M.lookup fname summ
      return (foreignFunctionAnnotations fsum)
    _ -> return $! []

lookupArgumentSummary :: (IsValue v, SummarizeModule s)
                         => DependencySummary
                         -> s
                         -> v
                         -> Int
                         -> Maybe [ParamAnnotation]
lookupArgumentSummary ds ms val ix =
  case valueContent' val of
    FunctionC f ->
      case ix < length (functionParameters f) of
        False -> Just []
        True ->
          let annots = summarizeArgument (functionParameters f !! ix) ms
              uannots = userParameterAnnotations (libraryAnnotations ds) f ix
          in Just $! uannots ++ map fst annots
    ExternalFunctionC ef -> do
      let fname = identifierContent $ externalFunctionName ef
          summ = depSummary ds
      fsum <- M.lookup fname summ
      let ps = foreignFunctionParameters fsum
      case ix < length ps of
        -- Either this was a vararg or the function was cast to a
        -- strange type (with extra parameters) before being called.
        False -> Just []
        True -> Just $ parameterAnnotations (ps !! ix)
    _ -> Just []


-- Helpers

-- | FIXME: Need to consult some metadata here to get sign information
--
-- Convert an LLVM type to an external type.  Note that some types are
-- not supported in external interfaces (vectors and exotic floating
-- point types).
typeToCType :: Bool -> Type -> Maybe CType
typeToCType isUnsigned t = case t of
  TypeVoid -> return CVoid
  TypeInteger i ->
    case isUnsigned of
      False -> return $! CInt i
      True -> return $! CUInt i
  TypeFloat -> return CFloat
  TypeDouble -> return CDouble
  TypeArray _ t' -> do
    tt <- typeToCType isUnsigned t'
    return $! CPointer tt
  TypeFunction r ts _ -> do
    rt <- typeToCType False r
    tts <- mapM (typeToCType False) ts
    return $! CFunction rt tts
  TypePointer t' _ -> do
    tt <- typeToCType False t'
    return $! CPointer tt
  TypeStruct (Just n) _ _ -> return $! CStruct (sanitizeStructName n) []
  TypeStruct Nothing ts _ -> do
    tts <- mapM (typeToCType False) ts
    return $! CAnonStruct tts
  TypeFP128 -> Nothing
  TypeX86FP80 -> Nothing
  TypePPCFP128 -> Nothing
  TypeX86MMX -> Nothing
  TypeLabel -> Nothing
  TypeMetadata -> Nothing
  TypeVector _ _ -> Nothing

-- | Convert an LLVM linkage to a type more suitable for the summary
-- If this function returns a Linkage, the function is exported in the
-- shared library interface.  Private (internal linkage) functions are
-- not exported and therefore not shown in the interface.
toLinkage :: LinkageType -> Maybe Linkage
toLinkage l = case l of
  LTExternal -> Just LinkDefault
  LTAvailableExternally -> Just LinkDefault
  LTLinkOnceAny -> Just LinkWeak
  LTLinkOnceODR -> Just LinkWeak
  LTAppending -> Just LinkDefault
  LTInternal -> Nothing
  LTPrivate -> Nothing
  LTLinkerPrivate -> Nothing
  LTLinkerPrivateWeak -> Nothing
  LTLinkerPrivateWeakDefAuto -> Nothing
  LTDLLImport -> Just LinkDefault
  LTDLLExport -> Just LinkDefault
  LTExternalWeak -> Just LinkWeak
  LTCommon -> Just LinkDefault
  LTWeakAny -> Just LinkWeak
  LTWeakODR -> Just LinkWeak
