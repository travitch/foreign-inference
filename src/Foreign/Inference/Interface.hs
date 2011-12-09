{-# LANGUAGE DeriveGeneric, OverloadedStrings #-}
-- | This module defines an external representation of library
-- interfaces.  Individual libraries are represented by the
-- 'LibraryInterface'.  The analysis reads these in and writes these
-- out.
--
-- During the analysis, the dependencies of the current library are
-- represented using the 'DependencySummary', which is composed of
-- several 'LibraryInterface's.
module Foreign.Inference.Interface (
  -- * Types
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
  loadDependencies,
  loadDependencies'
  ) where

import GHC.Generics

import Data.Aeson
import Data.ByteString ( ByteString )
import qualified Data.ByteString.Lazy as LBS
import Data.HashMap.Strict ( HashMap )
import qualified Data.HashMap.Strict as M
import Data.Set ( Set )
import qualified Data.Set as S
import Data.List ( foldl' )
import System.FilePath

-- | The annotations that are specific to individual parameters.
data ParamAnnotation = PAArray !Int
                     | PANotNull
                     deriving (Show, Generic)
instance FromJSON ParamAnnotation
instance ToJSON ParamAnnotation

-- | The annotations that can apply at the 'ForeignFunction' level.
data FuncAnnotation = FAAllocator
                    deriving (Show, Generic)
instance FromJSON FuncAnnotation
instance ToJSON FuncAnnotation

-- | Define linkage types so that modules with overlapping symbol
-- definitions have a chance at being linked together.
data Linkage = LinkDefault
             | LinkWeak
             deriving (Show, Generic)
instance FromJSON Linkage
instance ToJSON Linkage

-- | A simple external representation of C/C++ types.  Note that C++
-- templates are not (and will not) be represented.
data CType = CVoid
           | CChar
           | CUChar
           | CShort
           | CUShort
           | CInt
           | CUInt
           | CLong
           | CULong
           | CLongLong
           | CULongLong
           | CFloat
           | CDouble
           | CFunction CType [CType]
           | CPointer CType
           | CStruct String [CType]
           deriving (Show, Generic)
instance FromJSON CType
instance ToJSON CType

-- | Descriptions of 'ForeignFunction' parameters
data Parameter = Parameter { parameterType :: CType
                           , parameterName :: String
                           , parameterAnnotations :: [ParamAnnotation]
                           }
               deriving (Show, Generic)
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
                     deriving (Show, Generic)
instance FromJSON ForeignFunction
instance ToJSON ForeignFunction


-- | A description of a foreign library.  This is just a collection of
-- ForeignFunctions that also tracks its name and dependencies.
data LibraryInterface = LibraryInterface { libraryFunctions :: [ForeignFunction]
                                         , libraryName :: String
                                         , libraryDependencies :: [String]
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
            deriving (Show)

-- | A call
--
-- > loadDependencies summaryDir deps
--
-- Loads all of the 'LibraryInterface's transitively required by
-- @deps@ from the directory @summaryDir@.  Will throw an exception if
-- a required dependency is not found.
--
-- This variant will automatically include the C standard library (and
-- eventually the C++ standard library).
loadDependencies :: FilePath -> [String] -> IO DependencySummary
loadDependencies = loadDependencies' [CStdLib]

summaryExtension :: String
summaryExtension = "json"

-- | The same as 'loadDependencies', except it gives the option of not
-- automatically loading standard library summaries.
loadDependencies' :: [StdLib] -> FilePath -> [String] -> IO DependencySummary
loadDependencies' includeStd summaryDir deps = do
  m <- loadTransDeps summaryDir deps S.empty M.empty
  return (DS m)

-- | Load all of the dependencies requested (transitively).  This just
-- iterates loading interfaces and recording all of the new
-- dependencies until there are no more.
loadTransDeps :: FilePath -> [String] -> Set String -> DepMap -> IO DepMap
loadTransDeps summaryDir deps loadedDeps m = do
  let unmetDeps = filter (`S.member` loadedDeps) deps
      paths = map ((summaryDir </>) . (<.> summaryExtension)) unmetDeps
  case unmetDeps of
    [] -> return m
    _ -> do
      newInterfaces <- mapM parseInterface paths
      let newDeps = concatMap libraryDependencies newInterfaces
          newFuncs = concatMap libraryFunctions newInterfaces
          loadedDeps' = loadedDeps `S.union` S.fromList unmetDeps
          m' = foldl' mergeFunction m newFuncs
      loadTransDeps summaryDir newDeps loadedDeps' m'

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
      error $ "Functions with overlapping linkage: " ++ show f ++ " and " ++ show f'
  where
    fn = foreignFunctionName f

-- | FIXME: Convert this to catch IO exceptions and convert to a more
-- descriptive error type.
parseInterface :: FilePath -> IO LibraryInterface
parseInterface p = do
  c <- LBS.readFile p
  let mval = decode' c
  case mval of
    Nothing -> error $ "Failed to decode " ++ p
    Just li -> return li