{-# LANGUAGE TemplateHaskell, NoMonomorphismRestriction #-}
module Main ( main ) where

import Blaze.ByteString.Builder
import Blaze.ByteString.Builder.Char8
import Control.Monad ( when )
import qualified Data.ByteString.Lazy.Char8 as LBS
import Data.Default
import Data.HashSet ( HashSet )
import qualified Data.HashSet as HS
import Data.List ( find, intercalate, intersperse, partition )
import Data.Maybe ( mapMaybe )
import Data.Monoid
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
  let pyMod = {-# SCC "pyMod" #-} interfaceToCtypes libname iface
  LBS.putStrLn $ toLazyByteString pyMod

mconcatLines :: [Builder] -> Builder
mconcatLines = mconcat . intersperse (fromChar '\n')

-- | Load a library using ctypes.CDLL.  If an identifier is provided,
-- the resulting module object will be bound to it.
--
-- It first attempts to load the library.  If that fails, it strips
-- off a level of soname versioning and tries the less specific
-- version number.  This process is repeated recursively until the
-- only extension is .so.  At that point, the failing exception is
-- allowed to propagate up.
--
-- > try:
-- >   ctypes.CDLL('libfoo.so.0.1')
-- > except OSError:
-- >   try:
-- >     ctypes.CDLL('libfoo.so.0')
-- >   except OSError:
-- >     ctypes.CDLL('libfoo.so')
makeLibraryLoad :: Maybe (Ident ()) -> FilePath -> StatementQ ()
makeLibraryLoad ident fp = do
  ctypes <- captureName "ctypes"
  dllConstructor <- captureName "CDLL"
  modeKwd <- captureName "mode"
  modeName <- captureName "RTLD_GLOBAL"
  builtinName <- captureName commonBuiltinName
  osErrorName <- captureName "OSError"

  let conRef = makeDottedName [ ctypes, dllConstructor ]
      modeRef = makeDottedName [ ctypes, modeName ]
      errRef = makeDottedName [ builtinName, osErrorName ]
      call = callE conRef [ argExprA (stringE [fp]), argKeywordA modeKwd modeRef ]
      loadStmt = case ident of
        Nothing -> stmtExprS call
        Just i -> assignS [varE i] call
      catchClause = exceptClauseC (Just (errRef, Nothing))
      handler = handlerH catchClause [makeLibraryLoad ident base]

  -- If we are down to the very base soname (no more version
  -- extensions to strip off), let a failed load error out.
  -- Otherwise, try to load the next less-specific library.
  case ext == ".so" of
    True -> loadStmt
    False -> tryS [loadStmt] [handler] [] []
  where
    (base, ext) = splitExtension fp

interfaceToCtypes :: FilePath -> LibraryInterface -> Builder
interfaceToCtypes libName iface =
  mconcatLines [ runQ' header
               , mconcatLines typeDecls
               , mconcatLines typeDefs
               , mconcatLines funcs
               ]
  where
    header = do
      dllHandle <- captureName "_module"
      ptrTypeCacheName <- newName "_pointer_type_cache"
      resPtrName <- captureName "_RESOURCEPOINTER"

      let dll = makeLibraryLoad (Just dllHandle) libName
          deps = map (makeLibraryLoad Nothing) (libraryDependencies iface)

          ptrCacheInit = assignS [varE ptrTypeCacheName] (dictionaryE [])
          resPtrFunc = buildResPtrFunc resPtrName ptrTypeCacheName

      enumDecls <- mapM buildEnum (libraryEnums iface)
      moduleM $ concat [ importStatements
                       , deps
                       , [dll, ptrCacheInit, resPtrFunc]
                       , concat enumDecls
                       ]

    typeDecls = map (runQ' . buildTypeDecl . fst) (libraryTypes iface)
    typeDefs = map (runQ' . buildTypeDef . fst) (libraryTypes iface)

    funcs = map (runQ' . buildFunction) (libraryFunctions iface)
    runQ' = PP.prettyTextBuilder . runQ

commonBuiltinName :: String
commonBuiltinName = "_builtinModule"

-- | Import the ctypes module
importStatements :: [StatementQ ()]
importStatements = [ ctypesImp, builtinImp ]
  where
    ctypesImp = do
      ctypes <- captureName "ctypes"
      let ctypesImport = importItemI [ctypes] Nothing
      importS [ctypesImport]
    builtinImp = do
      v2builtins <- captureName "__builtin__"
      v3builtins <- captureName "builtins"
      commonName <- captureName commonBuiltinName
      impErrorName <- captureName "ImportError"
      let v2impitem = importItemI [v2builtins] (Just commonName)
          v3impitem = importItemI [v3builtins] (Just commonName)
          imperr = varE impErrorName
          importClause = exceptClauseC (Just (imperr, Nothing))
          handleImpErr = handlerH importClause [importS [v3impitem]]
      tryS [importS [v2impitem]] [handleImpErr] [] []

buildEnum :: CEnum -> Q [StatementQ ()]
buildEnum e = do
  className <- case null (enumName e) of
    True -> newName "AnonEnum"
    False -> captureName (enumName e)
  ctypes <- captureName "ctypes"
  cintName <- captureName "c_int"
  let parentName = makeDottedName [ ctypes, cintName ]
      classDecl = classS className [argExprA parentName] [passS]
      enumerationValues = map (buildEnumValue className) (enumValues e)
  return $! classDecl : enumerationValues
  where
    buildEnumValue className (valName, valValue) = do
      vName <- captureName valName
      let conCall = callE (varE className) [argExprA (intE valValue)]
      assignS [varE vName] conCall

-- | Initialize a type, but do not populate its fields yet.  Since
-- some fields may reference types that are not yet defined, we can't
-- instantiate them yet.  This is the first of the two-phase process.
-- This includes the __del__ method; the referenced _finalizer
-- attribute is only set within constructor functions.
--
-- > class TypeName(ctypes.Structure):
-- >   pass
--
-- It returns the name chosen for the struct, which may be mangled for
-- uniquenss.
buildTypeDecl :: CType -> StatementQ ()
buildTypeDecl (CStruct name _) = do
  className <- captureName name

  ctypes <- captureName "ctypes"
  struct <- captureName "Structure"

  let parentClass = makeDottedName [ ctypes, struct ]

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

-- | Build the RESOURCEPOINTER function
--
-- > def _RESOURCEPOINTER(cls):
-- >     try:
-- >        return _pointer_type_cache[cls]
-- >     except KeyError:
-- >         pass
-- >
-- >     klass = ctypes.POINTER(cls)
-- >     def doFinalize(self):
-- >       try:
-- >         if self._finalizer:
-- >           self._finalizer(self)
-- >       except AttributeError: pass
-- >
-- >     setattr(klass, "__del__", doFinalize)
-- >
-- >     _pointer_type_cache[cls] = klass
-- >     return klass
buildResPtrFunc :: Ident () -> Ident () -> StatementQ ()
buildResPtrFunc resPtrName cacheName = do
  clsParam <- newName "klass"

  builtinName <- captureName commonBuiltinName
  keyErrorName <- captureName "KeyError"
  attrErrorName <- captureName "AttributeError"

  -- > try:
  -- >   return _pointer_type_cache[klass]
  -- > except KeyError: pass
  let keyErrRef = makeDottedName [ builtinName, keyErrorName ]
      cacheRef = subscriptE (varE cacheName) (varE clsParam)
      tryAccess = returnS $ Just cacheRef
      accessClause = exceptClauseC $ Just (keyErrRef, Nothing)
      ignoreKeyError = handlerH accessClause [passS]
      cacheHit = tryS [tryAccess] [ignoreKeyError] [] []

  -- > cls = ctypes.POINTER(klass)
  resName <- newName "cls"
  ctypes <- captureName "ctypes"
  ptrName <- captureName "POINTER"
  let ptrCon = makeDottedName [ ctypes, ptrName ]
      ptrConCall = callE ptrCon [argExprA (varE clsParam)]
      resAssign = assignS [varE resName] ptrConCall

  -- > def doFinalize(self):
  -- >   try:
  -- >     if self._finalizer:
  -- >       self._finalizer(self)
  -- >   except AttributeError: pass
  finName <- newName "doFinalize"
  selfName <- newName "self"
  finFieldName <- captureName "_finalizer"
  let finFieldRef = makeDottedName [ selfName, finFieldName ]
      attrRef = makeDottedName [ builtinName, attrErrorName ]
      finCall = callE finFieldRef [argExprA (varE selfName)]
      condCall = conditionalS [(finFieldRef, [stmtExprS finCall])] []
      attrClause = exceptClauseC (Just (attrRef, Nothing))
      ignoreAttrError = handlerH attrClause [passS]
      tryFin = tryS [condCall] [ignoreAttrError] [] []
      finFunc = funS finName [paramP selfName Nothing Nothing] Nothing [tryFin]

  -- > setattr(cls, "__del__", doFinalize)
  setAttrName <- captureName "setattr"
  let attrCall = callE (varE setAttrName) [ argExprA (varE resName)
                                          , argExprA (stringE ["__del__"])
                                          , argExprA (varE finName)
                                          ]
      setAttr = stmtExprS attrCall

  -- > _pointer_type_cache[klass] = cls
  -- > return cls
  let cache = assignS [cacheRef] (varE resName)
      ret = returnS $ Just (varE resName)
      stmts = [cacheHit, resAssign, finFunc, setAttr, cache, ret]
  funS resPtrName [paramP clsParam Nothing Nothing] Nothing stmts

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
buildFunction :: ForeignFunction -> StatementQ ()
buildFunction f = do
  dllHandle <- captureName "_module"
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
      attachFinalizer = maybe [] ((:[]) . assignFinalizer dllHandle resultName) (find allocatorAnnotation (foreignFunctionAnnotations f))
      removeFinalizer = maybe [] clearFinalizer (find isFinalized nonOutputNames)
      nullGuards = mapMaybe buildNullGuard nonOutputNames
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
                     , nullGuards -- Checks for NULL params
                     , [dllCallResult] -- Call and save result
                     , attachFinalizer -- Attach finalizer if this is an allocator
                     , removeFinalizer -- Remove the finalizer if this is a finalizer (to avoid double frees)
                     , [dllReturn] -- Return result
                     ]
  let innerFunc = funS realFuncName ps Nothing stmts

  -- Another assignment:
  --
  -- > funcName = _funcName
  let overwriteFunc = assignS [varE fname] (varE realFuncName)

  -- Finally, call the function with the arguments provided
  --
  -- > return _funcName(...)
  let callArgs = map (argExprA . varE) (map snd nonOutputNames) -- paramNames
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

isFinalized :: (Parameter, Ident ()) -> Bool
isFinalized = any (==PAFinalize) . parameterAnnotations . fst

-- | Remove the finalizer from a value and then zero out its pointer.
--
-- > p._finalizer = None
-- > ctypes.memset(ctypes.addressof(p), 0, ctypes.sizeof(b))
--
-- The zeroing out prevents it from being used later accidentally, or
-- at least makes it easier to spot.
clearFinalizer :: (Parameter, Ident ()) -> [StatementQ ()]
clearFinalizer (_, pident) = [clear, zero]
  where
    clear = do
      finFieldName <- captureName "_finalizer"
      noneName <- captureName "None"
      let finFieldRef = makeDottedName [ pident, finFieldName ]
      assignS [finFieldRef] (varE noneName)
    zero = do
      ctypes <- captureName "ctypes"
      sizeofName <- captureName "sizeof"
      memsetName <- captureName "memset"
      addrOfName <- captureName "addressof"
      let pref = varE pident
          addrRef = makeDottedName [ ctypes, addrOfName ]
          sizeofRef = makeDottedName [ ctypes, sizeofName ]
          memsetRef = makeDottedName [ ctypes, memsetName]
          addrOf = callE addrRef [argExprA pref]
          sizeof = callE sizeofRef [argExprA pref]
      stmtExprS $ callE memsetRef [ argExprA addrOf
                                  , argExprA (intE (0 :: Int))
                                  , argExprA sizeof
                                  ]

-- | If the parameter is not nullable, return the check:
--
-- > if p.value == None or p.value == 0:
-- >   raise ValueError("Null pointer for argument p")
buildNullGuard :: (Parameter, Ident ()) -> Maybe (StatementQ ())
buildNullGuard (p, pident) =
  case any (==PANotNull) (parameterAnnotations p) of
    False -> Nothing
    True -> Just $ do
      builtinName <- captureName commonBuiltinName
      valueErrorName <- captureName "ValueError"

      let valErrRef = makeDottedName [ builtinName, valueErrorName ]
          test = unaryOpE notO (varE pident)
          ex = callE valErrRef [ argExprA (stringE ["Null pointer for argument " ++ parameterName p]) ]
          exVal = raiseExprV2C (Just (ex, Nothing))
          exStmt = raiseS exVal
      conditionalS [(test, [exStmt])] []


-- | Meant for use from the function builder for constructors.  This
-- assigns the correct finalizer to the @resultName@ of a low-level
-- allocator call.
--
-- Note that the assigned finalizer is the direct reference to
-- _module.finalizer; this is necessary to avoid some of the fancy
-- bookkeeping code present in the wrapped finalizer.
assignFinalizer :: Ident () -> Ident () -> FuncAnnotation -> StatementQ ()
assignFinalizer _ _ (FAAllocator "") =
  $failure "Unexpected empty allocator annotation"
assignFinalizer dllHandle resultName (FAAllocator fin) = do
  fieldName <- captureName "_finalizer"
  finalizerName <- captureName fin
  let fieldRef = makeDottedName [ resultName, fieldName ]
      finRef = makeDottedName [ dllHandle, finalizerName ]
  assignS [fieldRef] finRef
assignFinalizer _ _ _ = $failure "Unexpected annotation"

-- | Return True if this annotation provides the name of a finalizer.
allocatorAnnotation :: FuncAnnotation -> Bool
allocatorAnnotation (FAAllocator "") = False
allocatorAnnotation (FAAllocator _) = True
allocatorAnnotation _ = False

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
-- >   p = _arrTy(*p)
--
-- Note the *p in the final line; the list has to be expanded since
-- the array constructor does not take a list - it takes varargs.
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
    builtin <- captureName commonBuiltinName
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

        arrayConstructor = callE (varE arrayTypeName) [argExprA (starredE (varE ident))]
        arrayOverwrite = assignS [varE ident] arrayConstructor

        conversionBody = [ arrayTypeStmt, arrayOverwrite ]

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
      case parameterName p `HS.member` pythonKeywords of
        False -> captureName (parameterName p)
        True -> newName ('_' : parameterName p)
    True -> do
      -- If there was a dot, replacing it with the _ can't produce a
      -- keyword and this case is fine
      let name' = map replaceDot (parameterName p)
      newName name'

-- | Python keywords, augmented with some special functions required
-- for this library.  No param identifiers with these names will be
-- chosen.
pythonKeywords :: HashSet String
pythonKeywords =
  HS.fromList [ "and" , "as", "assert", "break", "class"
              , "continue", "def" , "del", "elif", "else"
              , "except", "exec", "finally", "for", "from"
              , "global", "if", "import", "in", "is", "lambda"
              , "not", "or", "pass", "print", "raise", "return"
              , "try", "while", "with", "yield", "True", "False"
              , "None"
                -- Functions/values
              , "_module", "_RESOURCEPOINTER", "ctypes", commonBuiltinName
              ]

replaceDot :: Char -> Char
replaceDot '.' = '_'
replaceDot c = c


-- | Translate the interface type to the associated ctypes type.
-- Note, the capture of _RESOURCEPOINTER here isn't exactly hygienic.
-- It is technically possible (though unlikely) to cause a problem.
-- To really be safe, function names and parameters would need to
-- avoid this identifier.  It could be added as a keyword, but
-- function names are not currently checked against that list.
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
      ptrCon <- captureName "_RESOURCEPOINTER"
      callE (varE ptrCon) [argExprA $ toCtype innerType]
    CStruct name _ -> captureName name >>= varE
    _ -> captureName "ctypes.c_void_p" >>= varE