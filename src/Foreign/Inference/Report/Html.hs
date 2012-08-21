{-# LANGUAGE OverloadedStrings, TemplateHaskell #-}
{-# OPTIONS_GHC -fno-warn-unused-do-bind #-}
module Foreign.Inference.Report.Html (
  SummaryOption(..),
  htmlIndexPage,
  htmlFunctionPage
  ) where

import Control.Arrow ( (&&&) )
import Control.Monad ( forM_, when )
import Data.ByteString.Lazy.Char8 ( ByteString, unpack )
import Data.List ( intercalate, partition, sort )
import Data.Maybe ( mapMaybe )
import Data.Map ( Map )
import qualified Data.Map as M
import Data.Monoid
import Data.Text ( Text, pack )
import qualified Data.Text as T
import Debug.Trace.LocationTH
import System.FilePath
import Text.Blaze.Html5 ( toValue, toHtml, (!), Html, AttributeValue )
import qualified Text.Blaze.Html5 as H
import qualified Text.Blaze.Html5.Attributes as A
import qualified Text.Highlighting.Kate as K
import Text.Highlighting.Kate.Types ( defaultFormatOpts, FormatOptions(..) )

import LLVM.Analysis hiding ( toValue )

import Foreign.Inference.Interface
import Foreign.Inference.Interface.Metadata
import Foreign.Inference.Report.Types

-- | Options for generating the HTML summary page
data SummaryOption = LinkDrilldowns -- ^ Include links to the drilldown pages for each function
                   deriving (Eq)

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
      H.ul $ forM_ (functionParameters f) (drilldownArgumentEntry startLine r)

    toHtml funcName >> "(" >> commaSepList (zip [0..] args) (indexPageArgument r) >> ") -> "
    H.span ! A.class_ "code-type" $ toHtml (show fretType)
    let lang = sourceFileLanguage srcFile
        highlightedSrc = K.highlightAs lang (preprocessFunction functionText)
        fmtOpts = defaultFormatOpts { numberLines = True
                                    , startNumber = startLine
                                    , lineAnchors = True
                                    }
    K.formatHtmlBlock fmtOpts highlightedSrc
    H.script ! A.type_ "text/javascript" $ H.preEscapedToMarkup (initialScript calledFunctions)

  where
    funcName = identifierContent (functionName f)
    pageTitle = funcName `mappend` " [function breakdown]"
    allInstructions = concatMap basicBlockInstructions (functionBody f)
    calledFunctions = foldr (extractCalledFunctionNames aliasReverseIndex) [] allInstructions
    m = reportModule r
    aliasReverseIndex = foldr indexAliases mempty (moduleAliases m)
    args = functionParameters f
    fretType = case functionType f of
      TypeFunction rt _ _ -> rt
      rtype -> rtype

-- | Determine the language type for the file.  Attempt a basic match
-- against the filename.  If this fails, strip off extensions until
-- something matches or there are no more extensions.  If it cannot be
-- determined, assume C.
sourceFileLanguage :: FilePath -> String
sourceFileLanguage p
  | not (hasExtension p) = "C"
  | otherwise =
    case K.languagesByFilename p of
      [] -> sourceFileLanguage (dropExtension p)
      lang : _ -> lang

indexAliases :: GlobalAlias -> Map Function [GlobalAlias] -> Map Function [GlobalAlias]
indexAliases a m =
  case globalAliasTarget a of
    FunctionC f -> M.insertWith' (++) f [a] m
    GlobalAliasC a' -> indexAliases a' m
    _ -> m

-- | Replace tabs with two spaces.  This makes the line number
-- highlighting easier to read.
preprocessFunction :: ByteString -> String
preprocessFunction = foldr replaceTab "" . unpack
  where
    replaceTab '\t' acc = ' ' : ' ' : acc
    replaceTab c acc = c : acc

extractCalledFunctionNames :: Map Function [GlobalAlias] -> Instruction -> [(Text, Text)] -> [(Text, Text)]
extractCalledFunctionNames aliasReverseIndex i acc =
  case valueContent' i of
    InstructionC CallInst { callFunction = cv } -> maybeExtract cv acc
    InstructionC InvokeInst { invokeFunction = cv } -> maybeExtract cv acc
    _ -> acc
  where
    maybeExtract cv names =
      case valueContent cv of
        FunctionC f ->
          case M.lookup f aliasReverseIndex of
            Nothing ->
              let ic = identifierContent (functionName f)
              in (ic, ic) : names
            Just aliases ->
              let ic = identifierContent (functionName f)
                  aliasNames = map (identifierContent . globalAliasName) aliases
              in zip aliasNames (repeat ic) ++ names
        _ -> names

initialScript :: [(Text, Text)] -> Text
initialScript calledFuncNames = mconcat [ "$(window).bind(\"load\", function () {\n"
                                        , "  initializeHighlighting();\n"
                                        , "  linkCalledFunctions(["
                                        , funcNameList
                                        , "]);\n"
                                        , "});"
                                        ]
  where
    toJsTuple (txtName, target) = mconcat ["['", txtName, "', '", target, "']"]
    quotedNames = map toJsTuple calledFuncNames
    funcNameList = T.intercalate ", " quotedNames


drilldownArgumentEntry :: Int -> InterfaceReport -> Argument -> Html
drilldownArgumentEntry startLine r arg = H.li $ do
  H.span ! A.class_ "code-type" $ toHtml (show (argumentType arg))
  H.a ! A.href "#" ! A.onclick (H.preEscapedToValue clickScript) $ toHtml argName
  drilldownArgumentAnnotations startLine annots
  where
    argName = identifierContent (argumentName arg)
    clickScript = mconcat [ "highlight('", argName, "');" ]
    annots = concatMap (summarizeArgument arg) (reportSummaries r)

drilldownArgumentAnnotations :: Int -> [(ParamAnnotation, [Witness])] -> Html
drilldownArgumentAnnotations _ [] = return ()
drilldownArgumentAnnotations startLine annots = do
  H.span ! A.class_ "code-comment" $ do
    " /* ["
    commaSepList annots mkAnnotLink
    "] */"
  where
    mkAnnotLink (a, witnessLines)
      | null witnessLines = toHtml (show a)
      | otherwise =
        H.a ! A.href "#" ! A.onclick (H.preEscapedToValue clickScript) $ toHtml (show a)
      where
        clickScript = mconcat ["highlightLines("
                              , pack (show startLine)
                              , ", ["
                              , pack (intercalate "," (mapMaybe showWL witnessLines))
                              , "]);"
                              ]
        showWL (Witness i s) = do
          l <- instructionToLine i
          return $! mconcat [ "[", show l, ", '", s, "']" ]

instructionSrcLoc :: Instruction -> Maybe Metadata
instructionSrcLoc i =
  case filter isSrcLoc (instructionMetadata i) of
    [md] -> Just md
    _ -> Nothing
  where
    isSrcLoc m =
      case m of
        MetaSourceLocation {} -> True
        _ -> False

instructionToLine :: Instruction -> Maybe Int
instructionToLine i =
  case instructionSrcLoc i of
    Nothing -> Nothing
    Just (MetaSourceLocation _ r _ _) -> Just (fromIntegral r)
    m -> $failure ("Expected source location: " ++ show (instructionMetadata i))

-- | Generate an index page listing all of the functions in a module.
-- Each listing shows the parameters and their inferred annotations.
-- Each function name is a link to its source code (if it was found.)
htmlIndexPage :: InterfaceReport -> [SummaryOption] -> Html
htmlIndexPage r opts = H.docTypeHtml $ do
  H.head $ do
    H.title (toHtml pageTitle)
    H.link ! A.href "style.css" ! A.rel "stylesheet" ! A.type_ "text/css"
  H.body $ do
    H.h1 "Module Information"
    H.div ! A.id "module-info" $ do
      "Name: " >> toHtml (moduleIdentifier m)
    H.h1 "Exposed Functions"
    indexPageFunctionListing r (LinkDrilldowns `elem` opts) "exposed-functions" externsWithAliases
    H.h1 "Private Functions"
    indexPageFunctionListing r (LinkDrilldowns `elem` opts) "private-functions" privates
    H.h1 "Annotated Types"
    indexPageTypeListing r ts
  where
    pageTitle :: Text
    pageTitle = (moduleIdentifier m) `mappend` " summary report"
    m = reportModule r
    ts = moduleInterfaceStructTypes m
    (externs, ps) = partition isExtern (moduleDefinedFunctions m)
    privates = map tagName ps
    externsWithAliases = map tagName externs ++ exposedAliases

    tagName f = (f, identifierAsString (functionName f))

    isExtern :: (HasVisibility a) => a -> Bool
    isExtern f = isVisible f && isExternLinkage f

    isVisible :: (HasVisibility a) => a -> Bool
    isVisible v =
      case valueVisibility v of
        VisibilityHidden -> False
        _ -> True

    isExternLinkage :: (HasVisibility a) => a -> Bool
    isExternLinkage v =
      case valueLinkage v of
        LTExternal -> True
        LTAvailableExternally -> True
        LTDLLExport -> True
        LTExternalWeak -> True
        _ -> False

    exposedAliases :: [(Function, String)]
    exposedAliases = mapMaybe externAliasToFunc (moduleAliases m)

    externAliasToFunc a
      | not (isExtern a) = Nothing
      | otherwise =
        case globalAliasTarget a of
          FunctionC f ->
            let internalName = identifierAsString (functionName f)
            in Just $ (f { functionName = globalAliasName a }, internalName)
          _ -> Nothing

class HasVisibility a where
  valueVisibility :: a -> VisibilityStyle
  valueLinkage :: a -> LinkageType

instance HasVisibility Function where
  valueVisibility = functionVisibility
  valueLinkage = functionLinkage

instance HasVisibility GlobalAlias where
  valueVisibility = globalAliasVisibility
  valueLinkage = globalAliasLinkage

indexPageTypeListing :: InterfaceReport -> [CType] -> Html
indexPageTypeListing r ts = do
  H.div ! A.id "annotated-types" $ do
    H.ul $ do
      forM_ ts' indexPageAnnotatedType
  where
    ts' = filter (not . null . snd) $ map (id &&& annotateType) (sort ts)
    annotateType t = concatMap (map fst . summarizeType t) (reportSummaries r)

indexPageAnnotatedType :: (CType, [TypeAnnotation]) -> Html
indexPageAnnotatedType (t, annots) = do
  H.li $ do
    H.span $ toHtml (show t)
    " "
    H.span ! A.class_ "code-comment" $ toHtml ("/* " ++ (show annots) ++ " */")


indexPageFunctionListing :: InterfaceReport -> Bool -> AttributeValue -> [(Function, String)] -> Html
indexPageFunctionListing r linkFuncs divId funcs = do
  H.div ! A.id divId $ do
    H.ul $ do
      forM_ funcs (indexPageFunctionEntry r linkFuncs)

indexPageFunctionEntry :: InterfaceReport -> Bool -> (Function, String) -> Html
indexPageFunctionEntry r linkFunc (f, internalName) = do
  H.li $ do
    H.span ! A.class_ "code" $ do
      case r of
        InterfaceReport { reportFunctionBodies = bodies } ->
          case M.lookup f bodies of
            Nothing -> toHtml fname
            Just _ -> do
              let drilldown = mconcat [ "functions/", internalName, ".html" ]
              case linkFunc of
                True -> H.a ! A.href (toValue drilldown) $ toHtml fname
                False -> toHtml fname
        _ -> toHtml fname
      "("
      commaSepList (zip [0..] args) (indexPageArgument r)
      ") -> "
      H.span ! A.class_ "code-type" $ toHtml (show fretType)
      functionAnnotations fannots
  where
    allAnnots = libraryAnnotations $ reportDependencies r
    fannots = concat [ userFunctionAnnotations allAnnots f
                     , concatMap (summarizeFunction f) (reportSummaries r)
                     ]
    fname = identifierContent (functionName f)
    -- Use a bit of trickery to flag when we need to insert commas
    -- after arguments (so we don't end up with a trailing comma in
    -- the argument list)
    args = functionParameters f
    fretType = case functionType f of
      TypeFunction rt _ _ -> rt
      rtype -> rtype

indexPageArgument :: InterfaceReport -> (Int, Argument) -> Html
indexPageArgument r (ix, arg) = do
  H.span ! A.class_ "code-type" $ do
    toHtml paramType
  " " >> toHtml paramName >> " " >> indexArgumentAnnotations annots
  where
    paramType = show (argumentType arg)
    paramName = identifierContent (argumentName arg)
    allAnnots = libraryAnnotations $ reportDependencies r
    annots = concat [ userParameterAnnotations allAnnots (argumentFunction arg) ix
                    , concatMap (map fst . summarizeArgument arg) (reportSummaries r)
                    ]

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
