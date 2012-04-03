{-# LANGUAGE TemplateHaskell #-}
module Main ( main ) where

import Control.Monad ( when )
import Data.Default
import Data.HashSet ( HashSet )
import qualified Data.HashSet as S
import Data.List ( find, intercalate, partition )
import Data.Maybe ( mapMaybe )
import Debug.Trace.LocationTH
import System.Console.CmdArgs.Explicit
import System.Console.CmdArgs.Text
import System.Exit
import System.FilePath
import Text.Printf

import Foreign.Inference.Interface
import Language.Python.Common.Builder hiding ( Parameter )
import qualified Language.Python.Common.Pretty as PP
import Language.Python.Common.PrettyAST ()

setHelp :: Opts -> Opts
setHelp opts = opts { wantsHelp = True }

setInterface :: String -> Opts -> Either String Opts
setInterface i opts = Right opts { interfaceFile = i : (interfaceFile opts) }

data Opts = Opts { wantsHelp :: Bool
                 , interfaceFile :: [FilePath]
                 }
          deriving (Show)

instance Default Opts where
  def = Opts { wantsHelp = False
             , interfaceFile = []
             }

cmdOpts :: Mode Opts
cmdOpts = mode "IIGen" def desc ifaceArg as
  where
    ifaceArg = flagArg setInterface "FILE"
    desc = "The code generator that consumes interface descriptions"
    as = [ flagHelpSimple setHelp
         ]

showHelpAndExit :: Mode a -> IO b -> IO b
showHelpAndExit args exitCmd = do
  putStrLn $ showText (Wrap 80) $ helpText [] HelpFormatOne args
  exitCmd

main :: IO ()
main = do
  opts <- processArgs cmdOpts

  when (wantsHelp opts) (showHelpAndExit cmdOpts exitSuccess)
  when (length (interfaceFile opts) /= 1) (showHelpAndExit cmdOpts exitFailure)

  let [ inFile ] = interfaceFile opts
      libname = takeBaseName inFile
  iface <- readLibraryInterface inFile
  let pyMod = interfaceToCtypes libname iface
  putStrLn $ PP.prettyText $ runQ pyMod

dependencyImport :: String -> StatementQ ()
dependencyImport lib = do
  ctypes <- captureName "ctypes"
  dllConstructor <- captureName "CDLL"
  modeKwd <- captureName "mode"
  modeName <- captureName "RTLD_GLOBAL"
  let conRef = makeDottedName [ ctypes, dllConstructor ]
      modeRef = makeDottedName [ ctypes, modeName ]
      call = callE conRef [ argExprA (stringE [lib]), argKeywordA modeKwd modeRef]
  stmtExprS call

interfaceToCtypes :: FilePath -> LibraryInterface -> ModuleQ ()
interfaceToCtypes libName iface = do
  dllHandle <- newName "_module"
  ctypes <- captureName "ctypes"
  dllConstructor <- captureName "CDLL"
  let dllCon = makeDottedName [ ctypes, dllConstructor ]
  let dllCall = callE dllCon [argExprA (stringE [libName])]
      -- Loads the shared library
      dll = assignS [varE dllHandle] dllCall
      deps = map dependencyImport (libraryDependencies iface)

      typeDecls = map buildTypeDecl (libraryTypes iface)
      typeDefs = map buildTypeDef (libraryTypes iface)

      funcs = map (buildFunction dllHandle) (libraryFunctions iface)

      defs = concat [ [importStatements]
                    , deps
                    , [dll]
                    , typeDecls
                    , typeDefs
                    , funcs
                    ]

  moduleM defs
  where
    -- | Import the ctypes module
    importStatements = do
      ctypes <- captureName "ctypes"
      builtins <- captureName "__builtin__"
      let ctypesImport = importItemI [ctypes] Nothing
          builtinImport = importItemI [builtins] Nothing
      importS [ctypesImport, builtinImport]

-- | Initialize a type, but do not populate its fields yet.  Since
-- some fields may reference types that are not yet defined, we can't
-- instantiate them yet.  This is the first of the two-phase process.
--
-- > class TypeName(ctypes.Structure): pass
buildTypeDecl :: CType -> StatementQ ()
buildTypeDecl (CStruct name _) = do
  ctypes <- captureName "ctypes"
  struct <- captureName "Structure"
  let parentClass = makeDottedName [ ctypes, struct ]

  className <- captureName name

  classS className [argExprA parentClass] [passS]
buildTypeDecl t = error ("Expected struct type: " ++ show t)

-- | Now define the fields of the struct:
--
-- TypeName._fields_ = [...]
buildTypeDef :: CType -> StatementQ ()
buildTypeDef (CStruct name members) = do
  className <- captureName name
  fields <- captureName "_fields_"
  let lhs = makeDottedName [ className, fields ]
      memberPairs = map toFieldPair members
  assignS [lhs] (listE memberPairs)
buildTypeDef t = error ("Expected struct type: " ++ show t)

-- | (fieldName, type)
toFieldPair :: (String, CType) -> ExprQ ()
toFieldPair (fieldName, ty) =
  tupleE [ stringE [fieldName], toCtype ty ]

isNotOutParam :: (Parameter, Ident ()) -> Bool
isNotOutParam (p, _) = not (PAOut `elem` parameterAnnotations p)

makeOutParamStorage :: (Parameter, Ident ()) -> StatementQ ()
makeOutParamStorage (p, pname) = do
  let CPointer innerType = parameterType p
  let conName = toCtype innerType
      conCall = callE conName []
  assignS [varE pname] conCall

byrefFunc :: ExprQ ()
byrefFunc = do
  ctypes <- captureName "ctypes"
  byref <- captureName "byref"
  makeDottedName [ ctypes, byref ]

-- | Build functions of the form:
--
-- > def funcName(...):
-- >   _module.funcName.argtypes = ...
-- >   _module.funcName.restype = ...
-- >   def _funcName(..):
-- >     _module.funcName(...)
-- >   funcName = _funcName
-- >   return _funcName(...)
--
-- The extra fluff is to delay the argument type setup until the
-- function is actually invoked.  Most won't be, so there is no need
-- to slow things down.  The overwriting assignment ensures that we
-- only set the types once.
--
-- The _module.funcName() form is efficient enough because the
-- function pointer is cached in the CDLL object.
--
-- Eventually, note that the docstring is specified twice.  The outer
-- wrapper needs one so that the docstring shows up before the
-- function is evaluated the first time.  The inner function needs it
-- so that it is still visible after the outer wrapper disappears.
buildFunction :: Ident () -> ForeignFunction -> StatementQ ()
buildFunction dllHandle f = do
  paramNames <- mapM findParameterName params
  let (nonOutputNames, outputNames) = partition isNotOutParam (zip params paramNames)
  fname <- captureName funcName
  let ps = map buildParam nonOutputNames
      docString = stringE [functionDocstring f]

  -- Make the assignment
  --
  -- > _module.funcName.argtypes = [...]
  argtypes <- captureName "argtypes"
  let argtypesRef = makeDottedName [ dllHandle, fname, argtypes ]
      argctypes = map (toCtype . parameterType) params
      argTypeAssign = assignS [argtypesRef] (listE argctypes)

  -- Make the assignment
  --
  -- > _module.funcName.restype = ...
  restype <- captureName "restype"
  let restypeRef = makeDottedName [ dllHandle, fname, restype ]
      resctype = toCtype (foreignFunctionReturnType f)
      restypeAssign = assignS [restypeRef] resctype

  -- Now build up the real (inner) function definition that makes the
  -- foreign call.
  realFuncName <- newName funcName
  resultName <- newName "result"
  let justOutVarNames = map snd outputNames
      arrayConversions = mapMaybe makeArrayConversion nonOutputNames
      dllFunc = makeDottedName [ dllHandle, fname ]
      dllCall = callE dllFunc (map (buildActualArg justOutVarNames) paramNames)
      dllCallResult = assignS [varE resultName] dllCall
      dllReturn =
        case (foreignFunctionReturnType f, null outputNames) of
          (CVoid, True) -> returnS Nothing
          (CVoid, False) -> returnS $ Just $ tupleE (map varE justOutVarNames)
          (_, True) -> returnS (Just (varE resultName))
          (_, False) -> returnS $ Just $ tupleE (varE resultName : map varE justOutVarNames)
      -- Make statements to allocate storage for output parameters.
      outParamStorage = map makeOutParamStorage outputNames
      stmts = concat [ [stmtExprS docString] -- outer docstring
                     , outParamStorage -- Allocations for out params
                     , arrayConversions
                     , [dllCallResult, dllReturn] -- Call and return
                     ]
  let innerFunc = funS realFuncName ps Nothing stmts

  -- Another assignment:
  --
  -- > funcName = _funcName
  let overwriteFunc = assignS [varE fname] (varE realFuncName)

  -- Finally, call the function with the arguments provided
  --
  -- > return _funcName(...)
  let callArgs = map (argExprA . varE) paramNames
  let callInner = returnS (Just (callE (varE realFuncName) callArgs))

  funS fname ps Nothing [ stmtExprS docString
                        , argTypeAssign
                        , restypeAssign
                        , innerFunc
                        , overwriteFunc
                        , callInner
                        ]
  where
    funcName = foreignFunctionName f
    params = foreignFunctionParameters f
    buildParam (_, pname) = paramP pname Nothing Nothing
    buildActualArg outNames name =
      case name `elem` outNames of
        False -> argExprA (varE name)
        True -> argExprA (callE byrefFunc [argExprA (varE name)])

-- | Generate a docstring for the given foreign function
functionDocstring :: ForeignFunction -> String
functionDocstring f = unlines $ filter (/="") [ts, arrParams]
  where
    ts :: String
    ts = printf "Type signature: %s(%s) -> %s" (foreignFunctionName f) paramTypes rtype
    paramTypes = intercalate ", " $ map (show . parameterType) normalParams
    rtype = case (foreignFunctionReturnType f, null outParams) of
      (CVoid, True) -> show (foreignFunctionReturnType f)
      (CVoid, False) -> printf "(%s)" (intercalate ", " (map (show . stripPointerType) outParamTypes))
      (_, True) -> show (foreignFunctionReturnType f)
      (_, False) -> printf "(%s)" (intercalate ", " (map show (foreignFunctionReturnType f : outParamTypes)))
    (normalParams, outParams) = partition notOutParam (foreignFunctionParameters f)
    outParamTypes = map parameterType outParams
    notOutParam p = not (PAOut `elem` parameterAnnotations p)
    arrayParams = filter isArrayTy (foreignFunctionParameters f)
    isArrayTy = any isPAArray . parameterAnnotations
    isPAArray (PAArray _) = True
    isPAArray _ = False

    arrParams = case null arrayParams of
      True -> ""
      False -> printf "Parameters %s can be C arrays or Python lists.  Modifications will not be written back to lists." (intercalate ", " (map parameterName arrayParams))

stripPointerType :: CType -> CType
stripPointerType (CPointer t) = t
stripPointerType t = $failure ("Expected pointer type: " ++ show t)

-- | If the parameter is an array parameter, construct a check to see
-- if the user's input is actually a list.  If it is, convert it to an
-- array.
--
-- Note: Only supports 1 dimensional arrays for now.
--
-- > if __builtin__.type(p) is __builtin__.list:
-- >   _arrTy = EltType * __builtin__.len(p)
-- >   p = _arrTy(p)
makeArrayConversion :: (Parameter, Ident ()) -> Maybe (StatementQ ())
makeArrayConversion (p, ident) = do
  -- Fails with Nothing if this is not an array parameter
  _ <- find isArray (parameterAnnotations p)
  let (itemType, knownLen) = case parameterType p of
        CPointer it -> (it, Nothing)
        CArray it n -> (it, Just n)
        _ -> $failure ("Unexpected non-array type: " ++ show (parameterType p))
      pyItemType = toCtype itemType
  return $ do
    builtin <- captureName "__builtin__"
    lenName <- captureName "len"
    typeName <- captureName "type"
    listName <- captureName "list"
    arrayTypeName <- newName "arrayType"
    let typeRef = makeDottedName [builtin, typeName]
        lenRef = makeDottedName [builtin, lenName]
        listRef = makeDottedName [builtin, listName]
    let paramType = callE typeRef [argExprA (varE ident)]
        typeTest = binaryOpE isO paramType listRef

        arrTyLen = case knownLen of
          Nothing -> callE lenRef [argExprA (varE ident)]
          Just n -> intE n
        arrTyEx = binaryOpE multiplyO pyItemType arrTyLen

        arrayTypeStmt = assignS [varE arrayTypeName] arrTyEx

        arrayConstructor = callE (varE arrayTypeName) [argExprA (varE ident)]
        arrayTypeOverwrite = assignS [varE arrayTypeName] arrayConstructor

        conversionBody = [ arrayTypeStmt, arrayTypeOverwrite ]

    conditionalS [(typeTest, conversionBody)] []
  where
    isArray (PAArray 1) = True
    isArray _ = False

-- | This may need to be extended if LLVM puts other strange
-- characters in identifiers
findParameterName :: Parameter -> Q (Ident ())
findParameterName p =
  case '.' `elem` parameterName p of
    False ->
      case parameterName p `S.member` pythonKeywords of
        False -> captureName (parameterName p)
        True -> newName ('_' : parameterName p)
    True -> do
      -- If there was a dot, replacing it with the _ can't produce a
      -- keyword and this case is fine
      let name' = map replaceDot (parameterName p)
      newName name'

pythonKeywords :: HashSet String
pythonKeywords =
  S.fromList [ "and" , "as", "assert", "break", "class"
             , "continue", "def" , "del", "elif", "else"
             , "except", "exec", "finally", "for", "from"
             , "global", "if", "import", "in", "is", "lambda"
             , "not", "or", "pass", "print", "raise", "return"
             , "try", "while", "with", "yield", "True", "False"
             ]

replaceDot :: Char -> Char
replaceDot '.' = '_'
replaceDot c = c


-- | Translate the interface type to the associated ctypes type.
toCtype :: CType -> ExprQ ()
toCtype ct =
  case ct of
    CVoid -> captureName "None" >>= varE
    CInt 1 -> captureName "ctypes.c_bool" >>= varE
    CInt 8 -> captureName "ctypes.c_int8" >>= varE
    CInt 16 -> captureName "ctypes.c_int16" >>= varE
    CInt 32 -> captureName "ctypes.c_int32" >>= varE
    CInt 64 -> captureName "ctypes.c_int64" >>= varE
    CInt _ -> error $ "Unexpected bit size: " ++ show ct
    CUInt 8 -> captureName "ctypes.c_uint8" >>= varE
    CUInt 16 -> captureName "ctypes.c_uint16" >>= varE
    CUInt 32 -> captureName "ctypes.c_uint32" >>= varE
    CUInt 64 -> captureName "ctypes.c_uint64" >>= varE
    CUInt _ -> error $ "Unexpected bit size: " ++ show ct
    CFloat -> captureName "ctypes.c_float" >>= varE
    CDouble -> captureName "ctypes.c_double" >>= varE
    CPointer (CInt 8) -> captureName "ctypes.c_char_p" >>= varE
    CPointer innerType -> do
      ptrCon <- captureName "ctypes.POINTER"
      callE (varE ptrCon) [argExprA $ toCtype innerType]
    CStruct name _ -> captureName name >>= varE
    _ -> captureName "ctypes.c_void_p" >>= varE