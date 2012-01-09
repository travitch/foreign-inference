module Foreign.Inference.Report.Types (
  -- * Types
  InterfaceReport(..)
  ) where

import Data.Map ( Map )
import Data.Text ( Text )
import Codec.Archive
import Data.LLVM
import Foreign.Inference.Interface

-- | An encapsulation of the report
data InterfaceReport =
  InterfaceReport { reportModule :: Module
                  , reportFunctionBodies :: Map Function (FilePath, Int, Text)
                  , reportArchive :: ArchiveIndex
                  , reportSummaries :: [ModuleSummary]
                  }
