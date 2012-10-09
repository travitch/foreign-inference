{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE OverloadedStrings #-}
-- {-# OPTIONS_GHC -fno-warn-unused-do-bind #-}
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
import Data.Text ( Text )
import qualified Data.Text as T
import Text.Hamlet ( shamlet )
import Text.Shakespeare.Text
import Text.Blaze.Html5 ( toValue, toHtml, (!), Html, AttributeValue )
import qualified Text.Blaze.Html5 as H
import qualified Text.Blaze.Html5.Attributes as A

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
htmlFunctionPage r f srcFile startLine functionText =
  [shamlet|
$doctype 5
<html>
  <head>
    <title>#{funcName} [function breakdown]
    <link rel=stylesheet href="../style.css" type="text/css">
    <link rel=stylesheet href="../codemirror.css" type="text/css">
    <script type="text/javascript" src="../jquery-1.7.1.js">
    <script type="text/javascript" src="../codemirror-compressed.js">
    <script type="text/javascript" src="../highlight.js">
    <script type="text/javascript" src="../code-highlighter.js">
  <body>
    Breakdown of #{funcName} (defined in #{srcFile})
    <div>
      <ul>
        $forall arg <- args
          <li>^{drilldownArgumentEntry startLine r arg}
        $if not (null fannots)
          <li>&rarr; <span class="code-comment">/* #{show fannots} */</span>
    <p>
      #{funcName} (#{sig}) -> <span class="code-type">#{show fretType}</span>
    <form>
      <textarea id="code" name="code">#{preprocessFunction functionText}
    <script type="text/javascript">
      #{H.preEscapedToMarkup (initialScript calledFunctions startLine)}
|]
  where
    funcName = identifierContent (functionName f)
    allInstructions = concatMap basicBlockInstructions (functionBody f)
    calledFunctions = foldr (extractCalledFunctionNames aliasReverseIndex) [] allInstructions
    sig = commaSepList args drilldownSignatureArgument
    m = reportModule r
    aliasReverseIndex = foldr indexAliases mempty (moduleAliases m)
    args = functionParameters f
    fretType = case functionType f of
      TypeFunction rt _ _ -> rt
      rtype -> rtype
    allAnnots = libraryAnnotations $ reportDependencies r
    fannots = concat [ userFunctionAnnotations allAnnots f
                     , concatMap (summarizeFunction f) (reportSummaries r)
                     ]

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

-- | This is the content of the script tag included after the code
-- snippet in each drilldown.  It invokes the syntax highlighter and
-- also links all of the functions called to their definitions (if
-- available).
initialScript :: [(Text, Text)] -> Int -> Text
initialScript calledFuncNames startLine =
  [st|
$(window).bind("load", function() {
  editor = CodeMirror.fromTextArea(document.getElementById("code"), {
    lineNumbers: true,
    firstLineNumber: #{show startLine},
    matchBrackets: true,
    mode: "text/x-csrc"
  });
  initializeHighlighting();
  linkCalledFunctions([#{funcNameList}]);
  });
|]
  where
    toJsTuple (txtName, target) = mconcat ["['", txtName, "', '", target, "']"]
    quotedNames = map toJsTuple calledFuncNames
    funcNameList = T.intercalate ", " quotedNames


drilldownArgumentEntry :: Int -> InterfaceReport -> Argument -> Html
drilldownArgumentEntry startLine r arg =
  [shamlet|
<span class="code-type">#{show (argumentType arg)}
  <a href="#" onclick="editor.highlightText('highlight', '#{argName}');">
    #{argName}
  #{drilldownArgumentAnnotations startLine annots}
|]
  where
    argName = identifierContent (argumentName arg)
    annots = concatMap (summarizeArgument arg) (reportSummaries r)

drilldownArgumentAnnotations :: Int -> [(ParamAnnotation, [Witness])] -> Html
drilldownArgumentAnnotations _ [] = return ()
drilldownArgumentAnnotations startLine annots =
  [shamlet| <span class="code-comment"> /* [ #{annotListing} ] */ </span> |]
  where
    annotListing = commaSepList annots mkAnnotLink
    showWL (Witness i s) = do
      l <- instructionToLine i
      return $! mconcat [ "[", show l, ", '", s, "']" ]
    mkAnnotLink (a, witnessLines)
      | null witnessLines = toHtml (show a)
      | otherwise =
        let clickScript = [st|highlightLines(#{show startLine}, [#{intercalate "," (mapMaybe showWL witnessLines)}]);|]
        in [shamlet| <a href="#" onclick="#{H.preEscapedToMarkup clickScript}">#{show a} |]

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
    m -> error ("Foreign.Inference.Report.Html.instructionToLine: Expected source location: " ++ show (instructionMetadata i))

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
      stringToHtml "Name: " >> toHtml (moduleIdentifier m)
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
    stringToHtml " "
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
      stringToHtml "("
      commaSepList (zip [0..] args) (indexPageArgument r)
      stringToHtml ") -> "
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

drilldownSignatureArgument :: Argument -> Html
drilldownSignatureArgument arg =
  [shamlet|
<span class="code-type">#{paramType}</span> #{paramName}
|]
  where
    paramType = show (argumentType arg)
    paramName = identifierContent (argumentName arg)

indexPageArgument :: InterfaceReport -> (Int, Argument) -> Html
indexPageArgument r (ix, arg) = do
  H.span ! A.class_ "code-type" $ toHtml paramType
  stringToHtml " " >> toHtml paramName >> stringToHtml " " >> indexArgumentAnnotations annots
  where
    paramType = show (argumentType arg)
    paramName = identifierContent (argumentName arg)
    allAnnots = libraryAnnotations $ reportDependencies r
    annots = concat [ userParameterAnnotations allAnnots (argumentFunction arg) ix
                    , concatMap (map fst . summarizeArgument arg) (reportSummaries r)
                    ]

indexArgumentAnnotations :: [ParamAnnotation] -> Html
indexArgumentAnnotations [] = return ()
indexArgumentAnnotations annots =
  H.span ! A.class_ "code-comment" $ do
    stringToHtml " /* ["
    commaSepList annots (toHtml . show)
    stringToHtml "] */"

functionAnnotations :: [FuncAnnotation] -> Html
functionAnnotations [] = return ()
functionAnnotations annots =
  H.span ! A.class_ "code-comment" $
    stringToHtml " /* [" >> commaSepList annots (toHtml . show) >> stringToHtml "] */"

-- Helpers


-- | Print out a comma-separated list of items (given a function to
-- turn those items into Html).  This handles the annoying details of
-- not accidentally printing a trailing comma.
commaSepList :: [a] -> (a -> Html) -> Html
commaSepList itms f =
  forM_ (zip itms commaTags) $ \(itm, tag) -> do
    f itm
    when tag (stringToHtml ", ")
  where
    commaTags = reverse $ False : replicate (length itms - 1) True

stringToHtml :: String -> Html
stringToHtml = toHtml
