{-# LANGUAGE DeriveGeneric, StandaloneDeriving #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Foreign.Inference.Interface.Types (
  LibraryInterface(..),
  Parameter(..),
  ForeignFunction(..),
  CEnum(..),
  CType(..),
  FuncAnnotation(..),
  ParamAnnotation(..),
  TypeAnnotation(..),
  Linkage(..)
  ) where

import GHC.Generics

import Data.Aeson
import Data.List ( intercalate )
import Text.Printf

import LLVM.Analysis.AccessPath

-- | The annotations that are specific to individual parameters.
--
-- Other annotations:
data ParamAnnotation = PAArray !Int
                     | PAOut
                     | PAOutAlloc String
                       -- ^ Allocator through an out parameter, with finalizer
                     | PAInOut
                     | PANotNull
                     | PAString
                     | PAConst
                     | PAFinalize
                     | PAUnref String [(String, [AccessType])] [String]
                     | PAAddRef String
                     | PAEscape
                     | PAContractEscape
                     | PAFptrEscape
                     | PAWillEscape
                     | PAScalarEffectAddOne String [AccessType]
                     | PAScalarEffectSubOne String [AccessType]
                     deriving (Show, Read, Generic, Eq, Ord)
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
                    deriving (Show, Read, Generic, Eq, Ord)
instance FromJSON FuncAnnotation
instance ToJSON FuncAnnotation

data TypeAnnotation = TARefCounted String String -- ^ The addRef and decRef functions
                    deriving (Show, Read, Generic, Eq, Ord)
instance FromJSON TypeAnnotation
instance ToJSON TypeAnnotation

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
           deriving (Eq, Ord, Generic)
instance FromJSON CType
instance ToJSON CType

instance Show CType where
  show CVoid = "void"
  show (CInt i) = "int" ++ show i
  show (CUInt i) = "uint" ++ show i
  show CFloat = "float"
  show CDouble = "double"
  show (CPointer (CInt 8)) = "string"
  show (CPointer (CUInt 8)) = "string"
  show (CPointer t) = show t ++"*"
  show (CArray t x) = printf "%s[%d]" (show t) x
  show (CStruct n _) = n
  show (CAnonStruct _) = "<anon>"
  show (CFunction rt ts) = printf "%s(%s)" (show rt) (intercalate ", " (map show ts))

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

data CEnum = CEnum { enumName :: String
                   , enumValues :: [(String, Int)]
                   }
           deriving (Eq, Ord, Show, Generic)
instance FromJSON CEnum
instance ToJSON CEnum

-- | A description of a foreign library.  This is just a collection of
-- ForeignFunctions that also tracks its name and dependencies.
data LibraryInterface = LibraryInterface { libraryFunctions :: [ForeignFunction]
                                         , libraryName :: String
                                         , libraryDependencies :: [String]
                                         , libraryTypes :: [(CType, [TypeAnnotation])]
                                         , libraryEnums :: [CEnum]
                                         }
                      deriving (Show, Generic)

instance FromJSON LibraryInterface
instance ToJSON LibraryInterface
