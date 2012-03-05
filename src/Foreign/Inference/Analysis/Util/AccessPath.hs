{-# LANGUAGE DeriveDataTypeable, FlexibleContexts #-}
module Foreign.Inference.Analysis.Util.AccessPath (
  -- * Types
  AccessPath,
  AccessPathError,
  -- * Constructor
  accessPath
  ) where

import Control.Exception
import Control.Failure
import Data.Typeable

import LLVM.Analysis

data AccessPathError = NoPathError Value
                     deriving (Typeable, Show)

instance Exception AccessPathError

-- | The sequence of field accesses used to reference a field
-- structure.
data AccessPath =
  AccessPath { accessPathBaseType :: Type
             , accessPathFields :: [Int]
             }

accessPath :: (Failure AccessPathError m) => Value -> m AccessPath
accessPath = undefined