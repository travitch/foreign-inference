{-# LANGUAGE DeriveGeneric #-}
module Foreign.Inference.Interface where

import GHC.Generics

import Data.ByteString ( ByteString )
import Data.Text ( Text )

data ParamAnnotation = PAArray !Int
                     | PANotNull
                     deriving (Show, Generic)

data FuncAnnotation = FAAllocator
                    deriving (Show, Generic)

-- | Define linkage types so that modules with overlapping symbol
-- definitions have a chance at being linked together.
data Linkage = LinkDefault
             | LinkWeak
             deriving (Show, Generic)

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
           | CStruct Text [CType]
           deriving (Show, Generic)

data Parameter = Parameter { parameterType :: CType
                           , parameterName :: Text
                           , parameterAnnotations :: [ParamAnnotation]
                           }
               deriving (Show, Generic)

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

-- | A description of a foreign library.  This is just a collection of
-- ForeignFunctions that also tracks its name and dependencies.
data LibraryInterface = LibraryInterface { libraryFunctions :: [ForeignFunction]
                                         , libraryName :: Text
                                         , libraryDependencies :: [Text]
                                         }
                      deriving (Show, Generic)
