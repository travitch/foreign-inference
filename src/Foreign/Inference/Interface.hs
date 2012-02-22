{-# LANGUAGE DeriveGeneric, OverloadedStrings, ExistentialQuantification, DeriveDataTypeable #-}
{-# LANGUAGE TemplateHaskell #-}
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
  DependencySummary,
  LibraryInterface(..),
  ForeignFunction(..),
  Parameter(..),
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
  summarizeArgument',
  summarizeFunction',
  readLibraryInterface
  ) where

import Prelude hiding ( catch )

import GHC.Generics

import Control.Exception
import Data.Aeson
import Data.ByteString.Char8 ( ByteString )
import qualified Data.ByteString.Char8 as SBS
import qualified Data.ByteString.Lazy as LBS
import Data.Data
import Data.HashMap.Strict ( HashMap )
import qualified Data.HashMap.Strict as M
import Data.Maybe ( mapMaybe )
import Data.Set ( Set )
import qualified Data.Set as S
import Data.List ( foldl' )
import FileLocation
import System.FilePath
import System.IO.Error hiding ( catch )

import Data.LLVM

import Paths_foreign_inference

-- | The extension used for all summaries
summaryExtension :: String
summaryExtension = "json"

data InterfaceException = DependencyMissing FilePath
                        | DependencyDecodeError FilePath
                        deriving (Show, Typeable)
instance Exception InterfaceException

-- | The annotations that are specific to individual parameters.
--
-- Other annotations:
data ParamAnnotation = PAArray !Int
                     | PAOut
                     | PAInOut
                     | PANotNull
                     | PAString
                     | PAConst
                     | PAFinalize
                     | PAEscape
                     | PAWillEscape
                     deriving (Show, Generic, Eq, Ord)
instance FromJSON ParamAnnotation
instance ToJSON ParamAnnotation

-- | The annotations that can apply at the 'ForeignFunction' level.
-- The FAVarArg annotation is not inferred but is still necessary.
--
-- Other annotations:
--
-- * FAReentrant (use to halt at runtime if called from different threads).
data FuncAnnotation = FAAllocator String -- ^ Record the associated finalizer
                    | FANoRet -- ^ The function does not return to the caller
                    | FAVarArg
                    deriving (Show, Generic, Eq, Ord)
instance FromJSON FuncAnnotation
instance ToJSON FuncAnnotation

-- | Define linkage types so that modules with overlapping symbol
-- definitions have a chance at being linked together.
data Linkage = LinkDefault
             | LinkWeak
             deriving (Eq, Ord, Show, Generic)
instance FromJSON Linkage
instance ToJSON Linkage

-- | A simple external representation of C/C++ types.  Note that C++
-- templates are not (and will not) be represented.
--
-- Opaque types are represented by a struct with an empty body.
data CType = CVoid
           | CInt !Int
           | CUInt !Int
           | CFloat
           | CDouble
           | CFunction CType [CType]
           | CPointer CType
           | CStruct String [CType]
           | CAnonStruct [CType]
           deriving (Eq, Ord, Show, Generic)
instance FromJSON CType
instance ToJSON CType

-- | Descriptions of 'ForeignFunction' parameters
data Parameter = Parameter { parameterType :: CType
                           , parameterName :: String
                           , parameterAnnotations :: [ParamAnnotation]
                           }
               deriving (Eq, Ord, Show, Generic)
instance FromJSON Parameter
instance ToJSON Parameter

-- | A description of the interface of a foreign function.  Note that
-- the function name is a ByteString to match the format it will have
-- in a shared library.
data ForeignFunction = ForeignFunction { foreignFunctionName :: ByteString
                                       , foreignFunctionLinkage :: Linkage
                                       , foreignFunctionReturnType :: CType
                                       , foreignFunctionParameters :: [Parameter]
                                       , foreignFunctionAnnotations :: [FuncAnnotation]
                                       }
                     deriving (Eq, Ord, Show, Generic)
instance FromJSON ForeignFunction
instance ToJSON ForeignFunction


-- | A description of a foreign library.  This is just a collection of
-- ForeignFunctions that also tracks its name and dependencies.
data LibraryInterface = LibraryInterface { libraryFunctions :: [ForeignFunction]
                                         , libraryName :: String
                                         , libraryDependencies :: [String]
                                         , libraryTypes :: [CType]
                                         }
                      deriving (Show, Generic)

instance FromJSON LibraryInterface
instance ToJSON LibraryInterface

type DepMap = HashMap ByteString ForeignFunction

-- | A summary of all of the functions that are dependencies of the
-- current library.
data DependencySummary = DS { depSummary :: DepMap }
                       deriving (Show)

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
data Witness = Witness Instruction String
             deriving (Eq, Ord, Show)

-- | An interface for analyses to implement in order to annotate
-- constructs in 'Module's.
class SummarizeModule s where
  summarizeArgument :: Argument -> s -> [(ParamAnnotation, [Witness])]
  summarizeFunction :: Function -> s -> [FuncAnnotation]

summarizeArgument' :: Argument -> ModuleSummary -> [(ParamAnnotation, [Witness])]
summarizeArgument' a (ModuleSummary s) = summarizeArgument a s

summarizeFunction' :: Function -> ModuleSummary -> [FuncAnnotation]
summarizeFunction' f (ModuleSummary s) = summarizeFunction f s

-- | An existential wrapper around types implementing
-- 'SummarizeModule' to allow heterogenous lists of analysis results.
data ModuleSummary = forall a . (SummarizeModule a) => ModuleSummary a

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
saveModule :: FilePath -> String -> [String] -> Module -> [ModuleSummary] -> IO ()
saveModule summaryDir name deps m summaries = do
  let i = moduleToLibraryInterface m name deps summaries
  saveInterface summaryDir i

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
  let deps' = foldl' addStdlibDeps deps includeStd
  predefinedSummaries <- getDataFileName "stdlibs"
  m <- loadTransDeps (predefinedSummaries : summaryDirs) deps' S.empty M.empty
  return (DS m)
  where
    addStdlibDeps ds CStdLib = "c" : "m" : ds
    addStdlibDeps ds CxxStdLib = "stdc++" : ds
    addStdlibDeps ds LLVMLib = "llvm" : ds

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
      $err' ("Functions with overlapping linkage: " ++ show f ++ " and " ++ show f')
  where
    fn = foreignFunctionName f

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
                            -> LibraryInterface
moduleToLibraryInterface m name deps summaries =
  LibraryInterface { libraryFunctions = funcs
                   , libraryTypes = types
                   , libraryName = name
                   , libraryDependencies = deps
                   }
  where
    -- | FIXME: Need a way to get all types from a Module Perhaps
    -- replace unsupported types with char[] of the equivalent number
    -- of bytes.
    types = [] -- map typeToCType []
    funcs = mapMaybe (functionToExternal summaries) (moduleDefinedFunctions m)

-- | Summarize a single function.  Functions with types in their
-- signatures that have certain exotic types are not supported in
-- interfaces.
functionToExternal :: [ModuleSummary] -> Function -> Maybe ForeignFunction
functionToExternal summaries f =
  case vis of
    VisibilityHidden -> Nothing
    _ -> do
      lnk <- toLinkage (functionLinkage f)
      fretty <- typeToCType fretType
      params <- mapM (paramToExternal summaries) (functionParameters f)
      return ForeignFunction { foreignFunctionName = identifierContent (functionName f)
                             , foreignFunctionLinkage =
                                  if vis == VisibilityProtected then LinkWeak else lnk
                             , foreignFunctionReturnType = fretty
                             , foreignFunctionParameters = params
                             , foreignFunctionAnnotations = annots
                             }
  where
    vis = functionVisibility f
    annots = concatMap (summarizeFunction' f) summaries
    fretType = case functionType f of
      TypeFunction rt _ _ -> rt
      t -> t

paramToExternal :: [ModuleSummary] -> Argument -> Maybe Parameter
paramToExternal summaries arg = do
  ptype <- typeToCType (argumentType arg)
  return Parameter { parameterType = ptype
                   , parameterName = SBS.unpack (identifierContent (argumentName arg))
                   , parameterAnnotations =
                     -- The map fst here drops witness information -
                     -- we don't need to expose that in summaries.
                     concatMap (map fst . summarizeArgument' arg) summaries
                   }

-- | Look up the summary information for the indicated parameter.
lookupArgumentSummary :: DependencySummary -> ExternalFunction -> Int -> Maybe [ParamAnnotation]
lookupArgumentSummary ds ef ix =
  case fsum of
    Nothing -> Nothing
    Just s -> case (isVarArg ef, ix < length (foreignFunctionParameters s)) of
      (True, False) -> Just [] -- Vararg and we don't have a summary for the given function
      (False, False) -> $err' ("lookupArgumentSummary: no parameter " ++ show ix ++ " for " ++ show ef)
      (_, True) -> Just $ parameterAnnotations (foreignFunctionParameters s !! ix)
  where
    fname = identifierContent $ externalFunctionName ef
    summ = depSummary ds
    fsum = M.lookup fname summ

lookupFunctionSummary :: DependencySummary -> ExternalFunction -> Maybe [FuncAnnotation]
lookupFunctionSummary ds ef = do
  let fname = identifierContent $ externalFunctionName ef
      summ = depSummary ds
  fsum <- M.lookup fname summ
  return (foreignFunctionAnnotations fsum)

isVarArg :: ExternalFunction -> Bool
isVarArg ef = isVa
  where
    (TypeFunction _ _ isVa) = externalFunctionType ef

-- Helpers

-- | FIXME: Need to consult some metadata here to get sign information
--
-- Convert an LLVM type to an external type.  Note that some types are
-- not supported in external interfaces (vectors and exotic floating
-- point types).
typeToCType :: Type -> Maybe CType
typeToCType t = case t of
  TypeVoid -> return CVoid
  TypeInteger i -> return $! CInt i
  TypeFloat -> return CFloat
  TypeDouble -> return CDouble
  TypeArray _ t' -> do
    tt <- typeToCType t'
    return $! CPointer tt
  TypeFunction r ts _ -> do
    rt <- typeToCType r
    tts <- mapM typeToCType ts
    return $! CFunction rt tts
  TypePointer t' _ -> do
    tt <- typeToCType t'
    return $! CPointer tt
  TypeStruct (Just n) _ _ -> return $! CStruct n []
  TypeStruct Nothing ts _ -> do
    tts <- mapM typeToCType ts
    return $! CAnonStruct tts
  TypeFP128 -> Nothing
  TypeX86FP80 -> Nothing
  TypePPCFP128 -> Nothing
  TypeX86MMX -> Nothing
  TypeLabel -> Nothing
  TypeMetadata -> Nothing
  TypeVector _ _ -> Nothing

-- FIXME: Use a different function to translate types that are going
-- to be used as type definitions at the beginning of a library
-- interface spec.  In that case, actually include the contained
-- types.

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
