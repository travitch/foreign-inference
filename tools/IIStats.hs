{-# LANGUAGE OverloadedStrings #-}
module Main ( main ) where

import Control.Monad ( forM_, when )
import Data.Default
import Data.Map ( Map )
import qualified Data.Map as M
import Data.Monoid
import qualified Data.Text.Lazy.IO as T
import System.Console.CmdArgs.Explicit
import System.Console.CmdArgs.Text
import System.Exit
import Text.Blaze.Html5 ( Html, toHtml )
import qualified Text.Blaze.Html5 as H
import Text.Blaze.Html.Renderer.Text as T

import Foreign.Inference.Interface

data Opts = Opts { wantsHelp :: Bool
                 , ignoredAnnotations :: [ParamAnnotation]
                 , interfaceFiles :: [FilePath]
                 }
          deriving (Show)

instance Default Opts where
  def = Opts { wantsHelp = False
             , ignoredAnnotations = []
             , interfaceFiles = []
             }

setHelp :: Opts -> Opts
setHelp o = o { wantsHelp = True }

addIgnored :: String -> Opts -> Either String Opts
addIgnored a o =
  case reads a of
    [(annot, "")] -> Right o { ignoredAnnotations = annot : ignoredAnnotations o }
    _ -> Left ("Invalid annotation " ++ a)

addInterface :: String -> Opts -> Either String Opts
addInterface f o = Right o { interfaceFiles = f : interfaceFiles o }

cmdOpts :: Mode Opts
cmdOpts = mode "IIStats" def desc ifaceArg as
  where
    ifaceArg = flagArg addInterface "FILE"
    desc = "Compute aggregate stats for interfaces"
    as = [ flagHelpSimple setHelp
         , flagReq ["ignore"] addIgnored "ANNOTATION" "Ignore an annotation.  Can be specified multiple times"
         ]

main :: IO ()
main = do
  opts <- processArgs cmdOpts
  when (wantsHelp opts) $ do
    putStrLn $ showText (Wrap 80) $ helpText [] HelpFormatOne cmdOpts
    exitSuccess

  interfaces <- mapM readLibraryInterface (interfaceFiles opts)
  let stats = map (interfaceStats (ignoredAnnotations opts)) interfaces
      h = renderStatsHTML stats
  T.putStrLn (T.renderHtml h)

renderStatsHTML :: [InterfaceStats] -> Html
renderStatsHTML stats = H.docTypeHtml $ do
  H.head $ do
    H.title "Aggregate Stats"
  H.body $ do
    mapM_ renderStatsTable stats
    renderStatsTable (mconcat stats)
    H.p $ do
      "Annotated Percent List = "
      toHtml (show pctList)
  where
    pctList = map annotatedFunctionPercent stats


renderStatsTable :: InterfaceStats -> Html
renderStatsTable stats = do
  H.h1 (toHtml (statsForLibrary stats))
  H.table $ do
    H.tr $ do
      H.td "Total Functions"
      H.td $ toHtml $ show $ statsTotalFunctions stats
    H.tr $ do
      H.td "Functions With Annotations"
      H.td $ toHtml $ show $ length (statsAnnotatedFunctions stats)
    H.tr $ do
      H.td "Total Annotations"
      H.td $ toHtml $ show $ statsTotalAnnotations stats
    H.tr $ do
      H.td "Percent With Annotations"
      H.td $ toHtml $ show $ annotatedFunctionPercent stats
    forM_ (M.toList (statsPerFuncAnnotation stats)) $ \(annot, lst) -> do
      H.tr $ do
        H.td $ toHtml (show annot)
        H.td $ toHtml $ show (length lst)
    forM_ (M.toList (statsPerParamAnnotation stats)) $ \(annot, lst) -> do
      H.tr $ do
        H.td $ toHtml (show annot)
        H.td $ toHtml $ show (length lst)

annotatedFunctionPercent :: InterfaceStats -> Double
annotatedFunctionPercent stats = annotLen / totalFuncs
  where
    annotLen :: Double
    annotLen = fromInteger $ toInteger $ length (statsAnnotatedFunctions stats)
    totalFuncs :: Double
    totalFuncs = fromInteger $ toInteger $ statsTotalFunctions stats

data InterfaceStats =
  InterfaceStats { statsForLibrary :: String
                 , statsTotalFunctions :: Int
                 , statsAnnotatedFunctions :: [ForeignFunction]
                 , statsPerParamAnnotation :: Map ParamAnnotation [Parameter]
                 , statsPerFuncAnnotation :: Map FuncAnnotation [ForeignFunction]
                 }

-- | Combine interface stats in a sane way.  The maps are updated with
-- unions.
instance Monoid InterfaceStats where
  mempty = InterfaceStats mempty 0 mempty mempty mempty
  mappend is1 is2 =
    InterfaceStats { statsForLibrary = "aggregate"
                   , statsTotalFunctions = statsTotalFunctions is1 + statsTotalFunctions is2
                   , statsAnnotatedFunctions = statsAnnotatedFunctions is1 ++ statsAnnotatedFunctions is2
                   , statsPerParamAnnotation = M.unionWith (++) (statsPerParamAnnotation is1) (statsPerParamAnnotation is2)
                   , statsPerFuncAnnotation = M.unionWith (++) (statsPerFuncAnnotation is1) (statsPerFuncAnnotation is2)
                   }

interfaceStats :: [ParamAnnotation] -> LibraryInterface -> InterfaceStats
interfaceStats ignored libIface =
  InterfaceStats { statsForLibrary = libraryName libIface
                 , statsTotalFunctions = length funcs
                 , statsAnnotatedFunctions = filter (funcHasAnnotation ignored) funcs
                 , statsPerParamAnnotation = foldr (collectParamAnnotations ignored) mempty params
                 , statsPerFuncAnnotation = foldr collectFuncAnnotations mempty funcs
                 }
  where
    params = concatMap foreignFunctionParameters funcs
    funcs = libraryFunctions libIface

statsTotalAnnotations :: InterfaceStats -> Int
statsTotalAnnotations is =
  length (concat (M.elems (statsPerParamAnnotation is))) +
    length (concat (M.elems (statsPerFuncAnnotation is)))

collectFuncAnnotations :: ForeignFunction
                          -> Map FuncAnnotation [ForeignFunction]
                          -> Map FuncAnnotation [ForeignFunction]
collectFuncAnnotations ff acc =
  foldr go acc (foreignFunctionAnnotations ff)
  where
    go annot = M.insertWith' (++) annot [ff]

collectParamAnnotations :: [ParamAnnotation]
                           -> Parameter
                           -> Map ParamAnnotation [Parameter]
                           -> Map ParamAnnotation [Parameter]
collectParamAnnotations ignored p acc =
  foldr go acc (parameterAnnotations p)
  where
    go annot m =
      case annot `elem` ignored of
        False -> M.insertWith' (++) annot [p] m
        True -> m

funcHasAnnotation :: [ParamAnnotation] -> ForeignFunction -> Bool
funcHasAnnotation ignored ff =
  not (null fannots) || any hasParamAnnotations params
  where
    fannots = foreignFunctionAnnotations ff
    params = foreignFunctionParameters ff
    hasParamAnnotations = not . null . filter notIgnored . parameterAnnotations
    notIgnored = not . (`elem` ignored)