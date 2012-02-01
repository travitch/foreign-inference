{-# LANGUAGE OverloadedStrings #-}
-- | This module contains a function to extract the definition of a
-- function from its source file.  The source file is determined based
-- on the Module metadata.
--
-- It uses efficient attoparsec parsers and blaze-builder to try to
-- save time and memory.
module Foreign.Inference.Report.FunctionText (
  getFunctionText
  ) where

import Blaze.ByteString.Builder
import Control.Applicative ( many )
import Data.Attoparsec.ByteString.Lazy ( Parser )
import qualified Data.Attoparsec.ByteString.Lazy as P
import Data.ByteString.Lazy.Char8 ( ByteString )
import qualified Data.ByteString.Char8 as BSC
import Data.Ascii ( ascii )
import Data.Monoid
import System.FilePath

import Codec.Archive
import Data.LLVM

isEndOfLine :: (Eq a, Num a) => a -> Bool
isEndOfLine w = w == 13 || w == 10

ignoreLine :: Parser ()
ignoreLine = do
  P.skipWhile (not . isEndOfLine)
  _ <- P.satisfy isEndOfLine
  return ()

-- | Extract the definition of the named function, which starts at
-- approximately the given line.
isolator :: Int -- ^ Approximate starting line number
            -> Parser ByteString
isolator line = do
  -- Skip many lines up to near the start of the function
  _ <- P.count (line - 1) ignoreLine

  -- We want the prefix of the function up until we see the opening
  -- curly brace.
  _ <- P.takeWhile (/= ascii '{')

  -- Now just match curly braces in a standard context-free way.
  -- FIXME: Ignore string literals, char literals, and comments
  body <- matchedBraces
  -- Ignore the rest
  _ <- P.takeLazyByteString

  return (toLazyByteString body)

matchedBraces :: Parser Builder
matchedBraces = do
  _ <- P.word8 (ascii '{')
  content <- many contentAndSubBody
  _ <- P.word8 (ascii '}')
  return $ mconcat [ fromByteString "{"
                   , mconcat content
                   , fromByteString "}"
                   ]

contentAndSubBody :: Parser Builder
contentAndSubBody = do
  pfx <- P.takeWhile (\c -> c /= ascii '{' && c /= ascii '}')
  P.choice [ nest pfx, blockEnd pfx ]
  where
    blockEnd :: BSC.ByteString -> Parser Builder
    blockEnd pfx =
      case BSC.null pfx of
        True -> fail "fail"
        False -> return (fromByteString pfx)
    nest pfx = do
      body <- matchedBraces
      rest <- contentAndSubBody
      return $ mconcat [ fromByteString pfx
                       , body
                       , rest
                       ]

-- | Make a best effort to find the implementation of the given
-- Function in its associated source archive.  The lookup is based on
-- debugging metadata (and will fail early if there is none).
--
-- From there, the starting line number of the function will be used
-- to try to isolate the body of the function in the file.
getFunctionText :: ArchiveIndex -> Function -> Maybe (FilePath, Int, ByteString)
getFunctionText a func = do
  let [md] = functionMetadata func
      md' = metaValueContent md
      line = metaSubprogramLine md'
  ctxt <- metaSubprogramContext md'

  let ctxt' = metaValueContent ctxt
      f = metaFileSourceFile ctxt'
      d = metaFileSourceDir ctxt'
      absSrcFile = BSC.unpack d </> BSC.unpack f

  bs <- entryContentSuffix a absSrcFile
  let functionText = P.parse (isolator (fromIntegral line)) bs

      mkTuple txt = Just (absSrcFile, fromIntegral line, txt)

  maybe Nothing mkTuple (P.maybeResult functionText)
