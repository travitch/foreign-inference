module Main ( main ) where

import Control.Monad ( when )
import qualified Data.ByteString.Lazy.Char8 as BS
import System.Console.CmdArgs.Explicit
import System.Console.CmdArgs.Text
import System.Exit

import Foreign.Inference.Interface
import Foreign.Inference.Interface.Diff

data Opts =
  Opts { outputFormat :: OutputFormat
       , inputs :: [FilePath]
       , wantsHelp :: Bool
       }

data OutputFormat = None
                  | Html
                  | Text
                  deriving (Eq, Ord, Show, Read)

defOpts :: Opts
defOpts = Opts Text [] False

cmdOpts :: Opts -> Mode Opts
cmdOpts defs = mode "InterfaceDiff" defs desc positionals as
  where
    desc = "A diff utility for interface descriptions"
    positionals = flagArg addInterface "[INTERFACE] [INTERFACE]"
    as = [ flagReq ["format", "f"] setFormat "FORMAT" "The output format.  One of None, Html, or Text (default Text)"
         , flagHelpSimple setHelp
         ]

setHelp :: Opts -> Opts
setHelp opts = opts { wantsHelp = True }

setFormat :: String -> Opts -> Either String Opts
setFormat f opts =
  case reads f of
    [] -> Left $ "Invalid format: " ++ f
    [(fmt, "")] -> Right opts { outputFormat = fmt }
    _ -> Left $ "Invalid format: " ++ f

addInterface :: String -> Opts -> Either String Opts
addInterface p opts
  | length (inputs opts) == 2 = Left "Exactly two interface files are required"
  | otherwise = Right opts { inputs = inputs opts ++ [p] }

showHelpAndExit :: Mode a -> IO b -> IO b
showHelpAndExit args exitCmd = do
  putStrLn $ showText (Wrap 80) $ helpText [] HelpFormatOne args
  exitCmd

main :: IO ()
main = do
  let arguments = cmdOpts defOpts
  opts <- processArgs arguments

  when (wantsHelp opts) (showHelpAndExit arguments exitSuccess)
  when (length (inputs opts) /= 2) (showHelpAndExit arguments exitFailure)

  let [oldPath, newPath] = inputs opts

  oldInterface <- readLibraryInterface oldPath
  newInterface <- readLibraryInterface newPath

  let diff = libraryDiff oldInterface newInterface

  case diff == emptyLibraryDiff of
    True -> exitSuccess
    False -> printDiff (outputFormat opts) diff

printDiff :: OutputFormat -> LibraryDiff -> IO ()
printDiff None _ = exitWith (ExitFailure 1)
printDiff Text diff =
  let bs = diffToByteString diff
  in BS.putStrLn bs >> exitWith (ExitFailure 1)
printDiff Html _ = error "HTML output is currently unimplemented"