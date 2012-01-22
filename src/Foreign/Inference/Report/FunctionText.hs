{-# LANGUAGE OverloadedStrings #-}
module Foreign.Inference.Report.FunctionText (
  getFunctionText
  ) where

import Control.Applicative ( many )
import Data.Attoparsec.ByteString.Char8 ( Parser )
import qualified Data.Attoparsec.ByteString.Char8 as P
import Data.ByteString.Char8 ( ByteString )
import qualified Data.ByteString.Char8 as BSC
import qualified Data.ByteString.Lazy.Char8 as LBSC
import System.FilePath

import Codec.Archive
import Data.LLVM

toStrict :: LBSC.ByteString -> ByteString
toStrict = BSC.concat . LBSC.toChunks

isolator :: Parser ByteString
isolator = do
  -- We want the prefix of the function up until we see the opening
  -- curly brace.
  pfx <- P.takeWhile (/= '{')

  -- Now just match curly braces in a standard context-free way.
  -- FIXME: Ignore string literals, char literals, and comments
  body <- matchedBraces
  -- Ignore the rest
  _ <- P.takeLazyByteString
  return (pfx `BSC.append` body)

matchedBraces :: Parser ByteString
matchedBraces = do
  _ <- P.char '{'
  content <- many contentAndSubBody
  _ <- P.char '}'
  return $ BSC.concat ["{", BSC.concat content, "}"]

contentAndSubBody :: Parser ByteString
contentAndSubBody = do
  pfx <- P.takeWhile (\c -> c /= '{' && c /= '}')
  P.choice [ nest pfx, blockEnd pfx ]
  where
    blockEnd :: ByteString -> Parser ByteString
    blockEnd pfx = do
      case BSC.null pfx of
        True -> fail "fail"
        False -> return pfx
    nest pfx = do
      body <- matchedBraces
      rest <- contentAndSubBody
      return $ BSC.concat [ pfx, body, rest ]

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
  let bs' = toStrict bs
      fident = identifierContent $ functionName func

      -- f starts on line number @line@.  We need to seek to that line
      -- and then search *backwards* for the function name (so we can
      -- get the arguments, too).
      (beforeCodeStart, codeStart) = splitAt (fromIntegral line) $ BSC.lines bs'
      (interestingCode, _) =
        foldr (findFuncName fident) (codeStart, True) beforeCodeStart

      -- f starts on line number line, so drop all of the lines up to
      -- there.  Then recombine the rest into a single Text that we
      -- can "parse".
      fileChunk = BSC.unlines interestingCode
      functionText = P.parseOnly isolator fileChunk
      mkTuple txt = Just (absSrcFile, fromIntegral line, txt)
  either (const Nothing) mkTuple functionText
  -- Now match curly braces and only keep what we accumulate until it
  -- drops back to zero.

-- Search backwards for the function name from the opening curly brace
-- using foldr.  Stop searching (and collecting chunks) when we find
-- the line with the function name in it.
--
-- This function may miss the return type, but that isn't a huge deal.
findFuncName :: ByteString
                -> ByteString
                -> ([ByteString], Bool)
                -> ([ByteString], Bool)
findFuncName _ _ a@(_, False) = a
findFuncName fname line (acc, True) =
  case fname `BSC.isInfixOf` line of
    False -> (line : acc, True)
    True -> (line : acc, False)
