{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleContexts #-}
-- | This module provides an interface for constructing, gathering,
-- and printing diagnostic information from various analyses.
--
-- It is an instance of 'Monoid' so that it can easily be used in a
-- Writer monad.
module Foreign.Inference.Diagnostics (
  -- * Types
  Location(..),
  Classification(..),
  Diagnostics,
  -- * Emitters
  emitDiagnosticInfo,
  emitDebugInfo,
  emitWarning,
  emitError,
  -- * Formatters
  formatDiagnostics
  ) where

import Control.Monad.Writer.Class
import Data.Monoid
import Data.Set ( Set, singleton )
import qualified Data.Set as S
import Text.Printf

-- | A source location.
data Location = Location { locationFilename :: String
                         , locationLine :: Int
                         }
              deriving (Eq, Ord, Show)

data Classification = Debug
                    | Info
                    | Warning
                    | Error
                    deriving (Eq, Ord, Read, Show)

data Diagnostic = Diagnostic { diagnosticLocation :: Maybe Location
                             , diagnosticType :: Classification
                             , diagnosticContent :: String
                             }
                deriving (Eq, Ord)

instance Show Diagnostic where
  show = showDiagnostic

showDiagnostic :: Diagnostic -> String
showDiagnostic Diagnostic { diagnosticLocation = Nothing
                          , diagnosticType = t
                          , diagnosticContent = msg
                          } =
  printf "[%s] %s" (show t) msg
showDiagnostic Diagnostic { diagnosticLocation = Just loc
                          , diagnosticType = t
                          , diagnosticContent = msg
                          } =
  printf "[%s] %s @ $s" (show t) msg (show loc)

-- | A set of diagnostics.  Diagnostics can be merged via the 'Monoid'
-- interface.
newtype Diagnostics = DS (Set Diagnostic)
                    deriving (Monoid)

-- | Emit fine-grained debugging information.
emitDebugInfo :: (MonadWriter Diagnostics m) => Maybe Location -> String -> m ()
emitDebugInfo loc msg = tell d
  where
    d = DS $ singleton $ Diagnostic loc Debug msg

-- | Add some diagnostic information to the current 'Diagnostics'.  This is
-- just information that may be informative the the caller.
emitDiagnosticInfo :: (MonadWriter Diagnostics m) => Maybe Location -> String -> m ()
emitDiagnosticInfo loc msg = tell d
  where
    d = DS $ singleton $ Diagnostic loc Info msg

-- | Add a warning diagnostic.  These are informational messages that
-- the user may want to do something about, but do not invalidate the
-- results at all.
emitWarning :: (MonadWriter Diagnostics m) => Maybe Location -> String -> m ()
emitWarning loc msg = tell d
  where
    d = DS $ singleton $ Diagnostic loc Warning msg

-- | Errors are diagnostics indicating that the results of an analysis
-- cannot be trusted.
emitError :: (MonadWriter Diagnostics m) => Maybe Location -> String -> m ()
emitError loc msg = tell d
  where
    d = DS $ singleton $ Diagnostic loc Error msg

-- | Print all of the classifications as or more severe than @c@ to
-- stdout.
--
-- > printDiagnostics c diags
formatDiagnostics :: Classification -> Diagnostics -> Maybe String
formatDiagnostics c (DS diags) =
  case S.null requestedDiags of
    True -> Nothing
    False -> Just $! formatDiags requestedDiags
  where
    isRequested x = LT /= x `compare` c
    requestedDiags = S.filter (isRequested . diagnosticType) diags

formatDiags :: Set Diagnostic -> String
formatDiags diags = unlines $ map show diagList
  where
    diagList = S.toList diags
