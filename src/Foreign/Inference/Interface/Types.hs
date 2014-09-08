{-# LANGUAGE DeriveGeneric, StandaloneDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
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

import Control.Applicative
import Control.DeepSeq
import Control.DeepSeq.Generics ( genericRnf )
import Control.Monad ( mzero )
import Data.Aeson as A
import qualified Data.Aeson.Types as A
import Data.IntMap ( IntMap )
import Data.List ( intercalate )
import qualified Data.Scientific as S
import Data.Set ( Set )
import Data.Text ( Text )
import qualified Data.Text as T
import qualified Data.Vector as V
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

instance A.FromJSON ParamAnnotation where
  parseJSON v = A.withObject "Param annotation" parseAnnot v
    where
      parseAnnot o = PAArray <$> o .: "PAArray"
                     <|> PAOut <$ hasKey o "PAOut"
                     <|> PAOutAlloc <$> o .: "PAOutAlloc"
                     <|> PAInOut <$ hasKey o "PAInOut"
                     <|> PANotNull <$ hasKey o "PANotNull"
                     <|> PAString <$ hasKey o "PAString"
                     <|> PAConst <$ hasKey o "PAConst"
                     <|> PAFinalize <$ hasKey o "PAFinalize"
                     <|> PAFinalizeField <$> o .: "PAFinalizeField"
                     <|> PAUnref <$> parseIndex o "PAUnref" 0 <*> parseIndex o "PAUnref" 1 <*> parseIndex o "PAUnref" 2
                     <|> PAAddRef <$> o .: "PAAddRef"
                     <|> PAEscape <$ hasKey o "PAEscape"
                     <|> PAArgEscape <$> o .: "PAArgEscape"
                     <|> PAContractEscape <$ hasKey o "PAContractEscape"
                     <|> PAFptrEscape <$ hasKey o "PAFptrEscape"
                     <|> PAWillEscape <$ hasKey o "PAWillEscape"
                     <|> PATransfer <$ hasKey o "PATransfer"
                     <|> PASAPWrite <$> o .: "PASAPWrite"
                     <|> PAScalarEffectAddOne <$> parseIndex o "PAScalarEffectAddOne" 0 <*> parseIndex o "PAScalarEffectAddOne" 1
                     <|> PAScalarEffectSubOne <$> parseIndex o "PAScalarEffectSubOne" 0 <*> parseIndex o "PAScalarEffectSubOne" 1

instance A.ToJSON ParamAnnotation where
  toJSON a =
    case a of
      PAArray dim -> A.object [ "PAArray" .= dim ]
      PAOut -> A.object [ "PAOut" .= () ]
      PAOutAlloc finalizer -> A.object [ "PAOutAlloc" .= finalizer ]
      PAInOut -> A.object [ "PAInOut" .= () ]
      PANotNull -> A.object [ "PANotNull" .= () ]
      PAString -> A.object [ "PAString" .= () ]
      PAConst -> A.object [ "PAConst" .= () ]
      PAFinalize -> A.object [ "PAFinalize" .= () ]
      PAFinalizeField fins -> A.object [ "PAFinalizeField" .= fins ]
      PAUnref f1 f2 f3 -> A.object [ "PAUnref" .= (f1, f2, f3) ]
      PAAddRef rf -> A.object [ "PAAddRef" .= rf ]
      PAEscape -> A.object [ "PAEscape" .= () ]
      PAArgEscape into -> A.object [ "PAArgEscape" .= into ]
      PAContractEscape -> A.object [ "PAContractEscape" .= () ]
      PAFptrEscape -> A.object [ "PAFptrEscape" .= () ]
      PAWillEscape -> A.object [ "PAWillEscape" .= () ]
      PATransfer -> A.object [ "PATransfer" .= () ]
      PASAPWrite targets -> A.object [ "PASAPWrite" .= targets ]
      PAScalarEffectAddOne fld ts -> A.object [ "PAScalarEffectAddOne" .= (fld, ts) ]
      PAScalarEffectSubOne fld ts -> A.object [ "PAScalarEffectSubOne" .= (fld, ts) ]

instance NFData ParamAnnotation where
  rnf = genericRnf

instance A.FromJSON AccessType where
  parseJSON v = A.withObject "Expected access type object" parseAT v
    where
      parseAT o = AccessField <$> o .: "AccessField"
                  <|> AccessUnion <$ hasKey o "AccessUnion"
                  <|> AccessArray <$ hasKey o "AccessArray"
                  <|> AccessDeref <$ hasKey o "AccessDeref"

instance A.ToJSON AccessType where
  toJSON at =
    case at of
      AccessField ix -> A.object [ "AccessField" .= ix ]
      AccessUnion -> A.object [ "AccessUnion" .= () ]
      AccessArray -> A.object [ "AccessArray" .= () ]
      AccessDeref -> A.object [ "AccessDeref" .= () ]

data ErrorActionArgument = ErrorInt Int
                         | ErrorString String
                         | ErrorArgument String Int
                           -- ^ Type and the position of the formal
                           -- argument being passed as an actual
                           -- argument
                         deriving (Show, Read, Generic, Eq, Ord)

instance A.FromJSON ErrorActionArgument where
  parseJSON v = A.withObject "Expected ErrorActionArgument object" parseEEA v
    where
      parseEEA o = ErrorInt <$> o .: "ErrorInt"
                   <|> ErrorString <$> o .: "ErrorString"
                   <|> ErrorArgument <$> parseIndex o "ErrorArgument" 0 <*> parseIndex o "ErrorArgument" 1

instance A.ToJSON ErrorActionArgument where
  toJSON e =
    case e of
      ErrorInt i -> A.object [ "ErrorInt" .= i ]
      ErrorString s -> A.object [ "ErrorString" .= s ]
      ErrorArgument s i -> A.object [ "ErrorArgument" .= (s, i) ]

parseIndex :: (A.FromJSON a) => A.Object -> Text -> Int -> A.Parser a
parseIndex o fld ix = A.withArray "Expected array elt" parseElt =<< o .: fld
  where
    parseElt a = atIndex a ix >>= A.parseJSON


instance NFData ErrorActionArgument where
  rnf = genericRnf

-- | These are actions that error handling code can perform that we
-- are interested in.  The most general characterization of these
-- actions is that they are the program actions that can allow the
-- function to pass information back to the caller (either in-band
-- return values or out-of-band routes).
data ErrorAction = AssignToGlobal String (Set Int)
                 | AssignToArgument String (Maybe (Set Int))
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

instance A.FromJSON ErrorAction where
  parseJSON = A.withObject "Expected ErrorAction object" parseEA
    where
      parseEA o = AssignToGlobal <$> parseIndex o "AssignToGlobal" 0 <*> parseIndex o "AssignToGlobal" 1
                  <|> AssignToArgument <$> parseIndex o "AssignToArgument" 0 <*> parseIndex o "AssignToArgument" 1
                  <|> AssignToCall <$> parseIndex o "AssignToCall" 0 <*> parseIndex o "AssignToCall" 1
                  <|> FunctionCall <$> parseIndex o "FunctionCall" 0 <*> parseIndex o "FunctionCall" 1

instance A.ToJSON ErrorAction where
  toJSON ea =
    case ea of
      AssignToGlobal s si -> A.object [ "AssignToGlobal" .= (s, si) ]
      AssignToArgument s msi -> A.object [ "AssignToArgument" .= (s, msi) ]
      AssignToCall s si -> A.object [ "AssignToCall" .= (s, si) ]
      FunctionCall s im -> A.object [ "FunctionCall" .= (s, im) ]

instance NFData ErrorAction where
  rnf = genericRnf

data ErrorReturn = ReturnConstantInt (Set Int)
                 | ReturnConstantPtr (Set Int)
                 deriving (Show, Read, Generic, Eq, Ord)

instance A.FromJSON ErrorReturn where
  parseJSON = A.withObject "Expected ErrorReturn object" parseER
    where
      parseER o = ReturnConstantInt <$> o .: "ReturnConstantInt"
                  <|> ReturnConstantPtr <$> o .: "ReturnConstantPtr"

instance A.ToJSON ErrorReturn where
  toJSON er =
    case er of
      ReturnConstantInt is -> A.object [ "ReturnConstantInt" .= is ]
      ReturnConstantPtr is -> A.object [ "ReturnConstantPtr" .= is ]

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

instance A.FromJSON FuncAnnotation where
  parseJSON = A.withObject "Expected FuncAnnotation object" parseFA
    where
      parseFA o = FAAllocator <$> o .: "FAAllocator"
                  <|> FANoRet <$ hasKey o "FANoRet"
                  <|> FAVarArg <$ hasKey o "FAVarArg"
                  <|> FACondFinalizer <$ hasKey o "FACondFinalizer"
                  <|> FASAPReturn <$> o .: "FASAPReturn"
                  <|> FAReportsErrors <$> parseIndex o "FAReportsErrors" 0 <*> parseIndex o "FAReportsErrors" 1
                  <|> FASuccessCodes <$> o .: "FASuccessCodes"

instance A.ToJSON FuncAnnotation where
  toJSON fa =
    case fa of
      FAAllocator finalizer -> A.object [ "FAAllocator" .= finalizer ]
      FANoRet -> A.object [ "FANoRet" .= () ]
      FAVarArg -> A.object [ "FAVarArg" .= () ]
      FACondFinalizer -> A.object [ "FACondFinalizer" .= () ]
      FASAPReturn acps -> A.object [ "FASAPReturn" .= acps ]
      FAReportsErrors eas er -> A.object [ "FAReportsErrors" .= (eas, er) ]
      FASuccessCodes scs -> A.object [ "FASuccessCodes" .= scs ]

instance NFData FuncAnnotation where
  rnf = genericRnf

data TypeAnnotation = TARefCounted String String -- ^ The addRef and decRef functions
                    deriving (Show, Read, Generic, Eq, Ord)

instance A.FromJSON TypeAnnotation where
  parseJSON = A.withObject "Expected TypeAnnotation object" parseTA
    where
      parseTA o = TARefCounted <$> parseIndex o "TARefCounted" 0 <*> parseIndex o "TARefCounted" 1

instance A.ToJSON TypeAnnotation where
  toJSON ta =
    case ta of
      TARefCounted iref dref -> A.object [ "TARefCounted" .= (iref, dref) ]

instance NFData TypeAnnotation where
  rnf = genericRnf

data ModuleAnnotation = MAErrorIndicators [String]
                      | MASuccessCodes [Int]
                      deriving (Show, Read, Generic, Eq, Ord)

instance A.FromJSON ModuleAnnotation where
  parseJSON = A.withObject "Expected ModuleAnnotation object" parseMA
    where
      parseMA o = MAErrorIndicators <$> o .: "MAErrorIndicators"
                  <|> MASuccessCodes <$> o .: "MASuccessCodes"

instance A.ToJSON ModuleAnnotation where
  toJSON ma =
    case ma of
      MAErrorIndicators ss -> A.object [ "MAErrorIndicators" .= ss ]
      MASuccessCodes scs -> A.object [ "MASuccessCodes" .= scs ]

instance NFData ModuleAnnotation where
  rnf = genericRnf

-- | Define linkage types so that modules with overlapping symbol
-- definitions have a chance at being linked together.
data Linkage = LinkDefault
             | LinkWeak
             deriving (Eq, Ord, Show, Generic)

instance A.FromJSON Linkage where
  parseJSON v = A.withObject "Linkage" parseLinkage v
    where
      parseLinkage o = LinkDefault <$ hasKey o "LinkDefault"
                       <|> LinkWeak <$ hasKey o "LinkWeak"
instance A.ToJSON Linkage where
  toJSON l =
    case l of
      LinkDefault -> A.object [ "LinkDefault" .= () ]
      LinkWeak -> A.object [ "LinkWeak" .= () ]

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

instance A.FromJSON CType where
  parseJSON v = A.withObject "Type object" parseType v
    where
      parseType o = CVoid <$ hasKey o "CVoid"
                    <|> CFloat <$ hasKey o "CFloat"
                    <|> CDouble <$ hasKey o "CDouble"
                    <|> CInt <$> o .: "CInt"
                    <|> CUInt <$> o .: "CUInt"
                    <|> CPointer <$> o .: "CPointer"
                    <|> CAnonStruct <$> o .: "CAnonStruct"
                    <|> (A.withArray "Expected array" parseArrayType =<< o .: "CArray")
                    <|> (A.withArray "Expected functype" parseFunctionType =<< o .: "CFunction")
                    <|> (A.withArray "Expected structtype" parseStructType =<< o .: "CStruct")
      parseArrayType :: A.Array -> A.Parser CType
      parseArrayType arr = do
        t <- A.parseJSON =<< atIndex arr 0
        len <- A.withScientific "Expected integer array length" parseInt =<< atIndex arr 1
        return $ CArray t len
      parseFunctionType arr = do
        v1 <- atIndex arr 0
        v2 <- atIndex arr 1
        CFunction <$> A.parseJSON v1 <*> A.parseJSON v2
      parseStructType arr = do
        v1 <- atIndex arr 0
        v2 <- atIndex arr 1
        name <- A.withText "Expected name" (return . T.unpack) v1
        CStruct <$> pure name <*> A.parseJSON v2
instance A.ToJSON CType where
  toJSON t =
    case t of
      CVoid -> A.object [ "CVoid" .= () ]
      CFloat -> A.object [ "CFloat" .= () ]
      CDouble -> A.object [ "CDouble" .= () ]
      CInt i -> A.object [ "CInt" .= i ]
      CUInt i -> A.object [ "CUInt" .= i ]
      CPointer t' -> A.object [ "CPointer" .= t' ]
      CArray t' n -> A.object [ "CArray" .= (t', n) ]
      CAnonStruct ts -> A.object [ "CAnonStruct" .= ts ]
      CStruct name ts -> A.object [ "CStruct" .= (name, ts) ]
      CFunction rt ts -> A.object [ "CFunction" .= (rt, ts) ]

parseInt :: S.Scientific -> A.Parser Int
parseInt s = case S.toBoundedInteger s of
  Nothing -> mzero
  Just i -> return i

atIndex :: A.Array -> Int -> A.Parser A.Value
atIndex a i = case a V.!? i of
  Nothing -> mzero
  Just v -> return v

hasKey :: A.Object -> Text -> A.Parser ()
hasKey o k = o .: k

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
