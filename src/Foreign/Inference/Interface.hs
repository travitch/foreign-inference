{-# LANGUAGE DeriveGeneric, OverloadedStrings, ExistentialQuantification, DeriveDataTypeable #-}
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

import GHC.Generics

import Control.Arrow ( (&&&) )
import Control.DeepSeq
import Control.Exception
import Data.Aeson
import Data.ByteString.Char8 ( ByteString )
import qualified Data.ByteString.Char8 as SBS
import qualified Data.ByteString.Lazy as LBS
import Data.Data
-- import Data.Dwarf
import Data.HashMap.Strict ( HashMap )
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as HS
import Data.Map ( Map )
import qualified Data.Map as Map
import Data.IntMap ( IntMap )
import qualified Data.IntMap as IM
import Data.Maybe ( mapMaybe )
import Data.Monoid
import Data.Set ( Set )
import qualified Data.Set as S
import Data.List ( foldl', stripPrefix )
import Debug.Trace.LocationTH
import System.FilePath
import System.IO.Error hiding ( catch )

import LLVM.Analysis
import LLVM.Analysis.AccessPath

import Foreign.Inference.Internal.TypeUnification

import Paths_foreign_inference

-- import Debug.Trace
-- debug = flip trace

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
                     | PAUnref
                     | PAEscape
                     | PAWillEscape
                     | PAScalarEffectAddOne String [AccessType]
                     | PAScalarEffectSubOne String [AccessType]
                     deriving (Show, Generic, Eq, Ord)
instance FromJSON ParamAnnotation
instance ToJSON ParamAnnotation

deriving instance Generic AccessType
instance FromJSON AccessType
instance ToJSON AccessType

-- | The annotations that can apply at the 'ForeignFunction' level.
-- The FAVarArg annotation is not inferred but is still necessary.
--
-- Other annotations:
--
-- * FAReentrant (use to halt at runtime if called from different threads).
data FuncAnnotation = FAAllocator String -- ^ Record the associated finalizer
                    | FANoRet -- ^ The function does not return to the caller
                    | FAVarArg
                    | FACondFinalizer
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
           | CArray CType !Int
           | CStruct String [(String, CType)]
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
data ForeignFunction = ForeignFunction { foreignFunctionName :: String
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
  let deps' = foldl' addStdlibDeps deps includeStd
  predefinedSummaries <- getDataFileName "stdlibs"
  m <- loadTransDeps (predefinedSummaries : summaryDirs) deps' S.empty M.empty
  return (DS m mempty)
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
                   , libraryTypes = opaqueTypes ++ types
                   , libraryName = name
                   , libraryDependencies = deps
                   }
  where
    -- FIXME Types need to be sorted such that any struct with a
    -- by-value struct member must come after that member.  There
    -- cannot be cycles in C here, so we can topsort.
    interfaceTypeMap = moduleInterfaceStructTypes m
    (unifiedTypes, ununifiedTypes) = unifyTypes (M.keys interfaceTypeMap)
    unifiedMDTypes = map (findTypeMD interfaceTypeMap) unifiedTypes
    types = mapMaybe metadataStructTypeToCType unifiedMDTypes
    uniqueOpaqueTypeNames = HS.toList $ HS.fromList $ map structTypeName ununifiedTypes
    opaqueTypes = map toOpaqueCType uniqueOpaqueTypeNames
    funcs = mapMaybe (functionToExternal summaries annots) (moduleDefinedFunctions m)

findTypeMD interfaceTypeMap t =
  case M.lookup t interfaceTypeMap of
    Nothing -> $failure ("No metadata found for type: " ++ show t)
    Just md -> (t, md)

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

paramMetaUnsigned :: Argument -> Bool
paramMetaUnsigned a =
  case argumentMetadata a of
    [] -> False
    [MetaDWLocal { metaLocalType = Just mt }] -> do
      case mt of
        MetaDWBaseType { metaBaseTypeEncoding = DW_ATE_unsigned } -> True
        MetaDWDerivedType { metaDerivedTypeParent = Just baseType } ->
          case baseType of
            MetaDWBaseType { metaBaseTypeEncoding = DW_ATE_unsigned } -> True
            _ -> False
        _ -> False
    _ -> False


paramTypeMetadata :: Argument -> Maybe Metadata
paramTypeMetadata a =
  case argumentMetadata a of
    [] -> Nothing
    [MetaDWLocal { metaLocalType = mt }] -> mt
    _ -> Nothing

functionReturnMetaUnsigned :: Function -> Bool
functionReturnMetaUnsigned f =
  case functionMetadata f of
    [] -> False
    [MetaDWSubprogram { metaSubprogramType = Just ftype }] ->
      case ftype of
        MetaDWCompositeType { metaCompositeTypeMembers = Just ms } ->
          case ms of
            MetadataList _ (Just rt : _) ->
              case rt of
                MetaDWDerivedType { metaDerivedTypeParent = Just baseType } ->
                  case baseType of
                    MetaDWBaseType { metaBaseTypeEncoding = DW_ATE_unsigned } -> True
                    _ -> False
                MetaDWBaseType { metaBaseTypeEncoding = DW_ATE_unsigned } -> True
                _ -> False
            _ -> False
        _ -> False
    _ -> False

functionReturnTypeMetadata :: Function -> Maybe Metadata
functionReturnTypeMetadata f =
  case functionMetadata f of
    [] -> Nothing
    [MetaDWSubprogram { metaSubprogramType = Just ftype }] ->
      case ftype of
        MetaDWCompositeType { metaCompositeTypeMembers = Just ms } ->
          case ms of
            MetadataList _ (rt : _) -> rt
            _ -> Nothing
        _ -> Nothing
    _ -> Nothing


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

moduleInterfaceStructTypes :: Module -> HashMap Type Metadata
moduleInterfaceStructTypes =
  foldr extractInterfaceTypes M.empty . moduleDefinedFunctions

extractInterfaceTypes :: Function -> HashMap Type Metadata -> HashMap Type Metadata
extractInterfaceTypes f m =
  foldr addTypeMdMapping m (mapMaybe isStructType typeMds)
  where
    TypeFunction rt _ _ = functionType f
    retMd = functionReturnTypeMetadata f
    argMds = map (argumentType &&& paramTypeMetadata) (functionParameters f)
    typeMds = (rt, retMd) : argMds
    addTypeMdMapping (llvmType, mdType) mdMap =
      case mdType of
        Nothing -> mdMap
        Just md -> M.insert llvmType md mdMap

--isStructType :: (Type, a) -> Maybe (Type, a)
isStructType (t@(TypeStruct _ _ _),
              Just MetaDWDerivedType { metaDerivedTypeTag = DW_TAG_typedef
                                , metaDerivedTypeParent = parent
                                }) =
  isStructType (t, parent)
isStructType (t@(TypeStruct _ _ _), a) = Just (t, a)
isStructType (TypePointer inner _,
              Just MetaDWDerivedType { metaDerivedTypeTag = DW_TAG_pointer_type
                                , metaDerivedTypeParent = parent
                                }) =
  isStructType (inner, parent)
isStructType (t@(TypePointer _ _),
              Just MetaDWDerivedType { metaDerivedTypeTag = DW_TAG_typedef
                                , metaDerivedTypeParent = parent}) =
  isStructType (t, parent)
isStructType _ = Nothing

sanitizeStructName :: String -> String
sanitizeStructName name = takeWhile (/= '.') name'
  where
    name' = case stripPrefix "struct." name of
      Nothing ->
        case stripPrefix "union." name of
          Nothing -> name
          Just x -> x
      Just x -> x

structTypeName :: Type -> String
structTypeName (TypeStruct (Just name) _ _) = sanitizeStructName name
structTypeName t = $failure ("Expected struct type: " ++ show t)

toOpaqueCType :: String -> CType
toOpaqueCType name = CStruct name []

metadataStructTypeToCType :: (Type, Metadata) -> Maybe CType
metadataStructTypeToCType (TypeStruct (Just name) members _,
                           MetaDWCompositeType { metaCompositeTypeMembers =
                                                    Just (MetadataList _ cmembers)
                                               }) = do
  let memberTypes = zip members cmembers
  mtys <- mapM trNameAndType memberTypes
  return (CStruct name mtys)
  where
    trNameAndType (llvmType, Just MetaDWDerivedType { metaDerivedTypeName = memberName
                                               }) = do
      realType <- structMemberToCType llvmType
      return (SBS.unpack memberName, realType)
    trNameAndType _ = Nothing
-- If there were no members in the metadata, this is an opaque type
metadataStructTypeToCType (TypeStruct (Just name) _ _, _) =
  return $! CStruct name []
metadataStructTypeToCType t =
  $failure ("Unexpected non-struct metadata: " ++ show t)

structMemberToCType :: Type -> Maybe CType
structMemberToCType t = case t of
  TypeInteger i -> return $! CInt i
  TypeFloat -> return CFloat
  TypeDouble -> return CDouble
  TypeArray n t' -> do
    tt <- structMemberToCType t'
    return $! CArray tt n
  TypeFunction r ts _ -> do
    rt <- structMemberToCType r
    tts <- mapM structMemberToCType ts
    return $! CFunction rt tts
  TypePointer t' _ -> do
    tt <- structMemberToCType t'
    return $! CPointer tt
  TypeStruct (Just n) _ _ ->
    let name' = sanitizeStructName n
    in return $! CStruct name' []
  TypeStruct Nothing ts _ -> do
    tts <- mapM structMemberToCType ts
    return $! CAnonStruct tts
  TypeVoid -> return $! CVoid -- Nothing
  TypeFP128 -> return $! CArray (CInt 8) 16
  -- Fake an 80 bit floating point number with an array of 10 bytes
  TypeX86FP80 -> return $! CArray (CInt 8) 10
  TypePPCFP128 -> return $! CArray (CInt 8) 16
  TypeX86MMX -> Nothing
  TypeLabel -> Nothing
  TypeMetadata -> Nothing
  TypeVector _ _ -> Nothing
