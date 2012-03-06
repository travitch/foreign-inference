{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleContexts #-}
-- | This module provides an interface for constructing, gathering,
-- and printing diagnostic information from various analyses.
--
-- It is an instance of 'Monoid' so that it can easily be used in a
-- Writer monad.
module Foreign.Inference.Diagnostics (
  -- * Class
  HasDiagnostics(..),
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

import Control.DeepSeq
import Control.Monad.Writer.Class
import Data.Lens.Common
import Data.Monoid
import Data.Set ( Set, singleton )
import qualified Data.Set as S
import Text.Printf

class HasDiagnostics a where
  diagnosticLens :: Lens a Diagnostics
  diagnosticLens = lens (const mempty) (\_ a -> a)
  -- addDiagnostics :: a -> Diagnostics -> a
  -- addDiagnostics a _ = a

  -- getDiagnostics :: a -> Diagnostics
  -- getDiagnostics _ = mempty

-- | A source location.
data Location = Location { locationFilename :: String
                         , locationLine :: !Int
                         }
              deriving (Eq, Ord, Show)

instance NFData Location where
  rnf l@(Location f _) =
    f `deepseq` l `seq` ()

data Classification = Debug
                    | Info
                    | Warning
                    | Error
                    deriving (Eq, Ord, Read, Show)

data Diagnostic = Diagnostic { diagnosticLocation :: Maybe Location
                             , diagnosticType :: !Classification
                             , diagnosticModule :: String
                             , diagnosticContent :: String
                             }
                deriving (Eq, Ord)

instance NFData Diagnostic where
  rnf d@(Diagnostic l _ m c) =
    l `deepseq` m `deepseq` c `deepseq` d `seq` ()

instance Show Diagnostic where
  show = showDiagnostic

showDiagnostic :: Diagnostic -> String
showDiagnostic Diagnostic { diagnosticLocation = Nothing
                          , diagnosticType = t
                          , diagnosticModule = m
                          , diagnosticContent = msg
                          } =
  printf "%s[%s] %s" (show t) m msg
showDiagnostic Diagnostic { diagnosticLocation = Just loc
                          , diagnosticType = t
                          , diagnosticModule = m
                          , diagnosticContent = msg
                          } =
  printf "%s[%s] %s @ $s" (show t) m msg (show loc)

-- | A set of diagnostics.  Diagnostics can be merged via the 'Monoid'
-- interface.
newtype Diagnostics = DS (Set Diagnostic)
                    deriving (Monoid)

instance NFData Diagnostics where
  rnf d@(DS s) = s `deepseq` d `seq` ()

-- | Emit fine-grained debugging information.
emitDebugInfo :: (MonadWriter Diagnostics m)
                 => Maybe Location -> String -> String -> m ()
emitDebugInfo loc modName msg = tell d
  where
    d = DS $ singleton $ Diagnostic loc Debug modName msg

-- | Add some diagnostic information to the current 'Diagnostics'.  This is
-- just information that may be informative the the caller.
emitDiagnosticInfo :: (MonadWriter Diagnostics m)
                      => Maybe Location -> String -> String -> m ()
emitDiagnosticInfo loc modName msg = tell d
  where
    d = DS $ singleton $ Diagnostic loc Info modName msg

-- | Add a warning diagnostic.  These are informational messages that
-- the user may want to do something about, but do not invalidate the
-- results at all.
emitWarning :: (MonadWriter Diagnostics m)
               => Maybe Location -> String -> String -> m ()
emitWarning loc modName msg = tell d
  where
    d = DS $ singleton $ Diagnostic loc Warning modName msg

-- | Errors are diagnostics indicating that the results of an analysis
-- cannot be trusted.
emitError :: (MonadWriter Diagnostics m)
             => Maybe Location -> String -> String -> m ()
emitError loc modName msg = tell d
  where
    d = DS $ singleton $ Diagnostic loc Error modName msg

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
