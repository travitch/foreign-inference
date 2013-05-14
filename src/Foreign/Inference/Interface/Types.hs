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
  ModuleAnnotation(..),
  Linkage(..),
  ErrorAction(..),
  ErrorActionArgument(..),
  ErrorReturn(..)
  ) where

import GHC.Generics

import Control.DeepSeq
import Control.DeepSeq.Generics ( genericRnf )
import Data.Aeson
import Data.IntMap ( IntMap )
import Data.List ( intercalate )
import Data.Set ( Set )
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
                     | PAFinalizeField [(String, [AccessType])]
                     | PAUnref String [(String, [AccessType])] [String]
                     | PAAddRef String
                     | PAEscape
                     | PAArgEscape !Int
                     | PAContractEscape
                     | PAFptrEscape
                     | PAWillEscape
                     | PATransfer
                     | PASAPWrite [(Int, String, [AccessType])]
                     | PAScalarEffectAddOne String [AccessType]
                     | PAScalarEffectSubOne String [AccessType]
                     deriving (Show, Read, Generic, Eq, Ord)
instance FromJSON ParamAnnotation
instance ToJSON ParamAnnotation

instance NFData ParamAnnotation where
  rnf = genericRnf

instance FromJSON AccessType
instance ToJSON AccessType

data ErrorActionArgument = ErrorInt Int
                         | ErrorString String
                         | ErrorArgument String Int
                           -- ^ Type and the position of the formal
                           -- argument being passed as an actual
                           -- argument
                         deriving (Show, Read, Generic, Eq, Ord)

instance FromJSON ErrorActionArgument
instance ToJSON ErrorActionArgument

instance NFData ErrorActionArgument where
  rnf = genericRnf

-- | These are actions that error handling code can perform that we
-- are interested in.  The most general characterization of these
-- actions is that they are the program actions that can allow the
-- function to pass information back to the caller (either in-band
-- return values or out-of-band routes).
data ErrorAction = AssignToGlobal String (Set Int)
                 | AssignToCall String (Set Int)
                   -- ^ Assign a constant int to the return value of a
                   -- call instruction
                 | FunctionCall String (IntMap ErrorActionArgument)
                   -- ^ A call to a function.  The list should not be
                   -- ints, but more descriptive wrappers.  We are
                   -- interested in constants (string and int) and
                   -- function arguments.  We may in the future be
                   -- interested in locals that are returned by
                   -- value...
                 deriving (Show, Read, Generic, Eq, Ord)

instance FromJSON ErrorAction
instance ToJSON ErrorAction

instance NFData ErrorAction where
  rnf = genericRnf

data ErrorReturn = ReturnConstantInt (Set Int)
                 | ReturnConstantPtr (Set Int)
                 deriving (Show, Read, Generic, Eq, Ord)

instance FromJSON ErrorReturn
instance ToJSON ErrorReturn

instance NFData ErrorReturn where
  rnf = genericRnf

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
                    | FASAPReturn [(Int, String, [AccessType])]
                    | FAReportsErrors (Set ErrorAction) ErrorReturn
                    | FASuccessCodes (Set Int)
                    deriving (Show, Read, Generic, Eq, Ord)
instance FromJSON FuncAnnotation
instance ToJSON FuncAnnotation

instance NFData FuncAnnotation where
  rnf = genericRnf

data TypeAnnotation = TARefCounted String String -- ^ The addRef and decRef functions
                    deriving (Show, Read, Generic, Eq, Ord)
instance FromJSON TypeAnnotation
instance ToJSON TypeAnnotation

instance NFData TypeAnnotation where
  rnf = genericRnf

data ModuleAnnotation = MAErrorIndicators [String]
                      deriving (Show, Read, Generic, Eq, Ord)

instance FromJSON ModuleAnnotation
instance ToJSON ModuleAnnotation

instance NFData ModuleAnnotation where
  rnf = genericRnf

-- | Define linkage types so that modules with overlapping symbol
-- definitions have a chance at being linked together.
data Linkage = LinkDefault
             | LinkWeak
             deriving (Eq, Ord, Show, Generic)
instance FromJSON Linkage
instance ToJSON Linkage
instance NFData Linkage

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

instance NFData CType where
  rnf = genericRnf

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

instance NFData Parameter where
  rnf = genericRnf

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

instance NFData ForeignFunction where
  rnf = genericRnf

data CEnum = CEnum { enumName :: String
                   , enumValues :: [(String, Int)]
                   }
           deriving (Eq, Ord, Show, Generic)
instance FromJSON CEnum
instance ToJSON CEnum

instance NFData CEnum where
  rnf = genericRnf

-- | A description of a foreign library.  This is just a collection of
-- ForeignFunctions that also tracks its name and dependencies.
data LibraryInterface = LibraryInterface { libraryFunctions :: [ForeignFunction]
                                         , libraryName :: String
                                         , libraryDependencies :: [String]
                                         , libraryTypes :: [(CType, [TypeAnnotation])]
                                         , libraryEnums :: [CEnum]
                                         , libraryAnnotations :: [ModuleAnnotation]
                                         }
                      deriving (Show, Generic)

instance FromJSON LibraryInterface
instance ToJSON LibraryInterface

instance NFData LibraryInterface where
  rnf = genericRnf
