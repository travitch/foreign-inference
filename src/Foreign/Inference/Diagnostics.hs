{-# LANGUAGE GeneralizedNewtypeDeriving #-}
-- | This module provides an interface for constructing, gathering,
-- and printing diagnostic information from various analyses.
--
-- It is an instance of 'Monoid' so that it can easily be used in a
-- Writer monad.
module Foreign.Inference.Diagnostics (
  Location(..),
  Diagnostic(..),
  Diagnostics
  ) where

import Data.Monoid
import Data.Set

data Location = Location { locationFilename :: String
                         , locationLine :: Int
                         }
              deriving (Eq, Ord)

data Diagnostic = Diagnostic { diagnosticLocation :: Maybe Location
                             , diagnosticContent :: String
                             }
                deriving (Eq, Ord)

newtype Diagnostics = DS (Set Diagnostic)
                    deriving (Monoid)