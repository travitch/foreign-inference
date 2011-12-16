module Main ( main ) where

import Data.Aeson
import qualified Data.Attoparsec.Lazy as L
import qualified Data.ByteString.Lazy as L
import System.Environment ( getArgs )

import Foreign.Inference.Interface

main :: IO ()
main = do
  [file] <- getArgs
  bs <- L.readFile file
  case L.parse json' bs of
    L.Done _ v ->
      let li :: Result LibraryInterface
          li = fromJSON v
      in case li of
        Error err -> error err
        Success r -> print r
    L.Fail inp ctxt es -> print (es, ctxt, inp)