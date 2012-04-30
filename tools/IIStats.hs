{-# LANGUAGE OverloadedStrings #-}
module Main ( main ) where

import Control.Monad ( forM_ )
import Data.Map ( Map )
import qualified Data.Map as M
import Data.Monoid
import qualified Data.Text.Lazy.IO as T
import System.Environment ( getArgs )
import Text.Blaze.Html5 ( Html, toHtml )
import qualified Text.Blaze.Html5 as H
import qualified Text.Blaze.Renderer.Text as T

import Foreign.Inference.Interface

main :: IO ()
main = do
  interfaceFiles <- getArgs
  interfaces <- mapM readLibraryInterface interfaceFiles
  let stats = map interfaceStats interfaces
      h = renderStatsHTML stats
  T.putStrLn (T.renderHtml h)

renderStatsHTML :: [InterfaceStats] -> Html
renderStatsHTML stats = H.docTypeHtml $ do
  H.head $ do
    H.title "Aggregate Stats"
  H.body $ do
    mapM_ renderStatsTable stats
    renderStatsTable (mconcat stats)

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
      let annotLen :: Double
          annotLen = fromInteger $ toInteger $ length (statsAnnotatedFunctions stats)
          totalFuncs :: Double
          totalFuncs = fromInteger $ toInteger $ statsTotalFunctions stats
      H.td $ toHtml $ show $ annotLen / totalFuncs
    forM_ (M.toList (statsPerFuncAnnotation stats)) $ \(annot, lst) -> do
      H.tr $ do
        H.td $ toHtml (show annot)
        H.td $ toHtml $ show (length lst)
    forM_ (M.toList (statsPerParamAnnotation stats)) $ \(annot, lst) -> do
      H.tr $ do
        H.td $ toHtml (show annot)
        H.td $ toHtml $ show (length lst)


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

interfaceStats :: LibraryInterface -> InterfaceStats
interfaceStats libIface =
  InterfaceStats { statsForLibrary = libraryName libIface
                 , statsTotalFunctions = length funcs
                 , statsAnnotatedFunctions = filter funcHasAnnotation funcs
                 , statsPerParamAnnotation = foldr collectParamAnnotations mempty params
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

collectParamAnnotations :: Parameter
                           -> Map ParamAnnotation [Parameter]
                           -> Map ParamAnnotation [Parameter]
collectParamAnnotations p acc =
  foldr go acc (parameterAnnotations p)
  where
    go annot = M.insertWith' (++) annot [p]

funcHasAnnotation :: ForeignFunction -> Bool
funcHasAnnotation ff =
  not (null fannots) || any hasParamAnnotations params
  where
    fannots = foreignFunctionAnnotations ff
    params = foreignFunctionParameters ff
    hasParamAnnotations = not . null . parameterAnnotations