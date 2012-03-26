module Main ( main ) where

import Control.Monad ( when )
import Data.Default
import System.Console.CmdArgs.Explicit
import System.Console.CmdArgs.Text
import System.Exit
import System.FilePath

import Foreign.Inference.Interface
import Language.Python.Common.Builder
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

interfaceToCtypes :: FilePath -> LibraryInterface -> ModuleQ ()
interfaceToCtypes libName iface = do
  dllHandle <- newName "_module"
  ctypes <- captureName "ctypes"
  dllConstructor <- captureName "CDLL"
  let dllCon = makeDottedName [ ctypes, dllConstructor ]
  let dllCall = callE dllCon [(argExprA (stringE [libName]))]
      -- Loads the shared library
      dll = assignS [varE dllHandle] dllCall

      funcs = map (buildFunction dllHandle) (libraryFunctions iface)

      defs = imp : dll : funcs

  moduleM defs
  where
    -- | Import the ctypes module
    imp = do
      ctypes <- captureName "ctypes"
      let itm = importItemI [ctypes] Nothing
      importS [itm]

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
-- Eventually, also tag on the docstring in the outer wrapper
buildFunction :: Ident () -> ForeignFunction -> StatementQ ()
buildFunction dllHandle f = do
  paramNames <- mapM (captureName . parameterName) params
  fname <- captureName funcName
  let ps = map buildParam (foreignFunctionParameters f)

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
  let dllFunc = makeDottedName [ dllHandle, fname ]
      dllCall = callE dllFunc (map (argExprA . varE) paramNames)
      dllReturn = returnS (Just dllCall)
  let innerFunc = funS realFuncName ps Nothing [dllReturn]

  -- Another assignment:
  --
  -- > funcName = _funcName
  let overwriteFunc = assignS [varE fname] (varE realFuncName)

  -- Finally, call the function with the arguments provided
  --
  -- > return _funcName(...)
  let callArgs = map (argExprA . varE) paramNames
  let callInner = returnS (Just (callE (varE realFuncName) callArgs))

  funS fname ps Nothing [ argTypeAssign
                        , restypeAssign
                        , innerFunc
                        , overwriteFunc
                        , callInner
                        ]
  where
    funcName = foreignFunctionName f
    params = foreignFunctionParameters f
    buildParam p = do
      pname <- captureName (parameterName p)
      paramP pname Nothing Nothing

-- | Translate the interface type to the associated ctypes type.
--
-- FIXME: Does not handle structs yet
toCtype :: CType -> ExprQ ()
toCtype ct =
  case ct of
    CVoid -> captureName "None" >>= varE
    CInt 1 -> captureName "ctypes.c_bool" >>= varE
    CInt 8 -> captureName "ctypes.c_char" >>= varE
    CInt 16 -> captureName "ctypes.c_short" >>= varE
    CInt 32 -> captureName "ctypes.c_int" >>= varE
    CInt 64 -> captureName "ctypes.c_longlong" >>= varE
    CInt _ -> error $ "Unexpected bit size: " ++ show ct
    CUInt 8 -> captureName "ctypes.c_uchar" >>= varE
    CUInt 16 -> captureName "ctypes.c_ushort" >>= varE
    CUInt 32 -> captureName "ctypes.c_uint" >>= varE
    CUInt 64 -> captureName "ctypes.c_ulonglong" >>= varE
    CUInt _ -> error $ "Unexpected bit size: " ++ show ct
    CFloat -> captureName "ctypes.c_float" >>= varE
    CDouble -> captureName "ctypes.c_double" >>= varE
    CPointer (CInt 8) -> captureName "ctypes.c_char_p" >>= varE
    CPointer innerType -> do
      ptrCon <- captureName "ctypes.POINTER"
      callE (varE ptrCon) [argExprA $ toCtype innerType]
    _ -> captureName "ctypes.c_void_p" >>= varE