{-# LANGUAGE OverloadedStrings #-}
module Foreign.Inference.Report.Html (
  htmlIndexPage,
  htmlFunctionPage
  ) where

import Control.Monad ( forM_, when )
import Data.List ( partition )
import qualified Data.Map as M
import Data.Monoid
import Data.Text ( Text )
import Data.Text.Encoding ( decodeUtf8 )
import qualified Data.Text as T
import Text.Blaze.Html5
import qualified Text.Blaze.Html5 as H
import qualified Text.Blaze.Html5.Attributes as A
import qualified Text.Highlighting.Kate as K
import qualified Text.XHtml as X

import Data.LLVM

import Foreign.Inference.Interface
import Foreign.Inference.Report.Types

htmlFunctionPage :: InterfaceReport -> Function -> FilePath -> Int -> Text -> Html
htmlFunctionPage r f srcFile startLine functionText = docTypeHtml $ do
  H.head $ do
    H.title (toHtml pageTitle)
    H.link ! A.href "../style.css" ! A.rel "stylesheet" ! A.type_ "text/css"
    H.link ! A.href "../hk-tango.css" ! A.rel "stylesheet" ! A.type_ "text/css"
  H.body $ do
    case highlightedSrc of
      Right (lang, srclines) -> do
        let fmtOpts = [ K.OptNumberLines
                      , K.OptNumberFrom startLine
                      , K.OptDetailed
                      , K.OptLineAnchors
                      ]
            xhtml = K.formatAsXHtml fmtOpts lang srclines
            xhtmlString = X.showHtmlFragment xhtml
        H.preEscapedString xhtmlString
      Left err -> do
        H.h3 $ H.toHtml $ "Error highlighting source: " ++ err
        H.pre $ toHtml functionText

  where
    pageTitle = "Breakdown of " `mappend` decodeUtf8 (identifierContent (functionName f))
    fileLang = K.languagesByFilename srcFile
    highlightedSrc = case fileLang of
      lang : _ ->
        case K.highlightAs lang (T.unpack functionText) of
          Left err -> Left err
          Right srcLines -> Right (lang, srcLines)
      _ -> Left ("No sytnax definition for file: " ++ srcFile)

htmlIndexPage :: InterfaceReport -> Html
htmlIndexPage r = docTypeHtml $ do
  H.head $ do
    H.title (toHtml pageTitle)
    H.link ! A.href "style.css" ! A.rel "stylesheet" ! A.type_ "text/css"
  H.body $ do
    H.h1 "Exposed Functions"
    indexPageFunctionListing r "exposed-functions" externs
    H.h1 "Private Functions"
    indexPageFunctionListing r "private-functions" privates
  where
    pageTitle :: Text
    pageTitle = "Summary report for " `mappend` decodeUtf8 (moduleIdentifier m)
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
      H.span ! A.class_ "code-type" $ do
        toHtml (show (functionType f))
  where
    fname = decodeUtf8 (identifierContent (functionName f))
    -- Use a bit of trickery to flag when we need to insert commas
    -- after arguments (so we don't end up with a trailing comma in
    -- the argument list)
    args = functionParameters f

indexPageArgument :: InterfaceReport -> Argument -> Html
indexPageArgument r arg = do
  H.span ! A.class_ "code-type" $ do
    toHtml paramType
  " "
  toHtml paramName
  indexArgumentAnnotations annots
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
