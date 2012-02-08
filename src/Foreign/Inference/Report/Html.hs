{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-unused-do-bind #-}
module Foreign.Inference.Report.Html (
  htmlIndexPage,
  htmlFunctionPage
  ) where

import Control.Monad ( forM_, when )
import Data.ByteString.Lazy.Char8 ( ByteString, unpack )
import Data.List ( partition )
import qualified Data.Map as M
import Data.Monoid
import Data.Text ( Text )
import Data.Text.Encoding ( decodeUtf8 )
import qualified Data.Text as T
import Text.Blaze.Html5 ( toValue, toHtml, (!), Html, AttributeValue )
import qualified Text.Blaze.Html5 as H
import qualified Text.Blaze.Html5.Attributes as A
import qualified Text.Highlighting.Kate as K
import Text.Highlighting.Kate.Types ( defaultFormatOpts, FormatOptions(..) )

import Data.LLVM

import Foreign.Inference.Interface
import Foreign.Inference.Report.Types

-- | This page is a drilled-down view for a particular function.  The
-- function body is syntax highlighted using the kate syntax
-- definitions.
--
-- FIXME: Provide a table of aggregate stats (counts of each inferred
-- annotation)
--
-- FIXME: It would also be awesome to include call graph information
-- (as in doxygen)
htmlFunctionPage :: InterfaceReport -> Function -> FilePath -> Int -> ByteString -> Html
htmlFunctionPage r f srcFile startLine functionText = H.docTypeHtml $ do
  H.head $ do
    H.title (toHtml pageTitle)
    H.link ! A.href "../style.css" ! A.rel "stylesheet" ! A.type_ "text/css"
    H.link ! A.href "../hk-tango.css" ! A.rel "stylesheet" ! A.type_ "text/css"
    H.script ! A.type_ "text/javascript" ! A.src "../jquery-1.7.1.js" $ return ()
    H.script ! A.type_ "text/javascript" ! A.src "../highlight.js" $ return ()
  H.body $ do
    "Breakdown of " >> toHtml funcName >> " defined in " >> toHtml srcFile
    H.div $ do
      H.ul $ forM_ (functionParameters f) (drilldownArgumentEntry r)

    toHtml funcName >> "(" >> commaSepList args (indexPageArgument r) >> ") -> "
    H.span ! A.class_ "code-type" $ toHtml (show fretType)
    let lang : _ = K.languagesByFilename srcFile
        highlightedSrc = K.highlightAs lang (unpack functionText)
        fmtOpts = defaultFormatOpts { numberLines = True
                                    , startNumber = startLine
                                    , lineAnchors = True
                                    }
    K.formatHtmlBlock fmtOpts highlightedSrc
    H.script ! A.type_ "text/javascript" $ H.preEscapedText (initialScript calledFunctions)

  where
    funcName = decodeUtf8 (identifierContent (functionName f))
    pageTitle = funcName `mappend` " [function breakdown]"
    allInstructions = concatMap basicBlockInstructions (functionBody f)
    calledFunctions = foldr extractCalledFunctionNames [] allInstructions
    args = functionParameters f
    fretType = case functionType f of
      TypeFunction rt _ _ -> rt
      rtype -> rtype

extractCalledFunctionNames :: Instruction -> [Text] -> [Text]
extractCalledFunctionNames i acc =
  case valueContent' i of
    InstructionC CallInst { callFunction = cv } -> maybeExtract cv acc
    InstructionC InvokeInst { invokeFunction = cv } -> maybeExtract cv acc
    _ -> acc
  where
    maybeExtract cv names =
      case valueContent cv of
        FunctionC f ->
          let fname = decodeUtf8 $ identifierContent (functionName f)
          in fname : names
        _ -> names

initialScript :: [Text] -> Text
initialScript calledFuncNames = mconcat [ "$(window).bind(\"load\", function () {\n"
                                        , "  initializeHighlighting();\n"
                                        , "  linkCalledFunctions(["
                                        , funcNameList
                                        , "]);\n"
                                        , "});"
                                        ]
  where
    quotedNames = map (\txt -> mconcat ["'", txt, "'"]) calledFuncNames
    funcNameList = T.intercalate ", " quotedNames


drilldownArgumentEntry :: InterfaceReport -> Argument -> Html
drilldownArgumentEntry r arg = H.li $ do
  H.span ! A.class_ "code-type" $ toHtml (show (argumentType arg))
  H.a ! A.href "#" ! A.onclick (H.preEscapedTextValue clickScript) $ toHtml argName
  indexArgumentAnnotations annots
  where
    argName = decodeUtf8 (identifierContent (argumentName arg))
    clickScript = mconcat [ "highlight('", argName, "');" ]
    annots = concatMap (summarizeArgument' arg) (reportSummaries r)

-- | Generate an index page listing all of the functions in a module.
-- Each listing shows the parameters and their inferred annotations.
-- Each function name is a link to its source code (if it was found.)
htmlIndexPage :: InterfaceReport -> Html
htmlIndexPage r = H.docTypeHtml $ do
  H.head $ do
    H.title (toHtml pageTitle)
    H.link ! A.href "style.css" ! A.rel "stylesheet" ! A.type_ "text/css"
  H.body $ do
    H.h1 "Module Information"
    H.div ! A.id "module-info" $ do
      "Name: " >> toHtml (decodeUtf8 (moduleIdentifier m))
    H.h1 "Exposed Functions"
    indexPageFunctionListing r "exposed-functions" externs
    H.h1 "Private Functions"
    indexPageFunctionListing r "private-functions" privates
  where
    pageTitle :: Text
    pageTitle = decodeUtf8 (moduleIdentifier m) `mappend` " summary report"
    m = reportModule r
    (externs, privates) =
      partition isExtern (moduleDefinedFunctions m)

    isExtern :: Function -> Bool
    isExtern Function { functionLinkage = l } =
      case l of
        LTExternal -> True
        LTAvailableExternally -> True
        LTDLLExport -> True
        LTExternalWeak -> True
        _ -> False

indexPageFunctionListing :: InterfaceReport -> AttributeValue -> [Function] -> Html
indexPageFunctionListing r divId funcs = do
  H.div ! A.id divId $ do
    H.ul $ do
      forM_ funcs (indexPageFunctionEntry r)

indexPageFunctionEntry :: InterfaceReport -> Function -> Html
indexPageFunctionEntry r f = do
  H.li $ do
    H.span ! A.class_ "code" $ do
      case M.lookup f (reportFunctionBodies r) of
        Nothing -> toHtml fname
        Just _ -> do
          let drilldown = mconcat [ "functions/", fname, ".html" ]
          H.a ! A.href (toValue drilldown) $ toHtml fname
      "("
      commaSepList args (indexPageArgument r)
      ") -> "
      H.span ! A.class_ "code-type" $ toHtml (show fretType)
      functionAnnotations fannots
  where
    fannots = concatMap (summarizeFunction' f) (reportSummaries r)
    fname = decodeUtf8 (identifierContent (functionName f))
    -- Use a bit of trickery to flag when we need to insert commas
    -- after arguments (so we don't end up with a trailing comma in
    -- the argument list)
    args = functionParameters f
    fretType = case functionType f of
      TypeFunction rt _ _ -> rt
      rtype -> rtype

indexPageArgument :: InterfaceReport -> Argument -> Html
indexPageArgument r arg = do
  H.span ! A.class_ "code-type" $ do
    toHtml paramType
  " " >> toHtml paramName >> " " >> indexArgumentAnnotations annots
  where
    paramType = show (argumentType arg)
    paramName = decodeUtf8 (identifierContent (argumentName arg))
    annots = concatMap (summarizeArgument' arg) (reportSummaries r)

indexArgumentAnnotations :: [ParamAnnotation] -> Html
indexArgumentAnnotations [] = return ()
indexArgumentAnnotations annots = do
  H.span ! A.class_ "code-comment" $ do
    " /* ["
    commaSepList annots (toHtml . show)
    "] */"

functionAnnotations :: [FuncAnnotation] -> Html
functionAnnotations [] = return ()
functionAnnotations annots = do
  H.span ! A.class_ "code-comment" $ do
    " /* [" >> commaSepList annots (toHtml . show) >> "] */"

-- Helpers


-- | Print out a comma-separated list of items (given a function to
-- turn those items into Html).  This handles the annoying details of
-- not accidentally printing a trailing comma.
commaSepList :: [a] -> (a -> Html) -> Html
commaSepList itms f =
  forM_ (zip itms commaTags) $ \(itm, tag) -> do
    f itm
    when tag $ do
      ", "
  where
    commaTags = reverse $ False : replicate (length itms - 1) True
