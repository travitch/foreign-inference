module Foreign.Inference.Report.Types (
  -- * Types
  InterfaceReport(..)
  ) where

import Data.ByteString.Lazy.Char8 ( ByteString )
import Data.Map ( Map )
import Codec.Archive
import Data.LLVM
import Foreign.Inference.Interface

-- | An encapsulation of the report
data InterfaceReport =
  InterfaceReport { reportModule :: Module
                  , reportFunctionBodies :: Map Function (FilePath, Int, ByteString)
                  , reportArchive :: ArchiveIndex
                  , reportSummaries :: [ModuleSummary]
                  }
