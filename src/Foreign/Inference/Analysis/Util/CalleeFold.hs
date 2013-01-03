module Foreign.Inference.Analysis.Util.CalleeFold (
  calleeArgumentFold
  ) where

import Control.Monad ( foldM )

import LLVM.Analysis
import LLVM.Analysis.PointsTo

-- | Abstracts the pattern of analyzing all possible callees at a call
-- site.
--
-- The call
--
-- > calleeArgumentFold f acc pta callee actualArgs
--
-- applies @f@ to each possible target of @callee@, once per actual
-- argument (paired with its 0-based index).  The accumulator is
-- threaded through to collect results.  The signature of @f@ should
-- be:
--
-- > f target acc (ix, actual)
--
-- Indirect call targets are resolved with the given points-to
-- analysis.
calleeArgumentFold :: (PointsToAnalysis pta, Monad m)
                      => (Value -> acc -> (Int, Value) -> m acc)
                      -> acc
                      -> pta
                      -> Value
                      -> [Value]
                      -> m acc
calleeArgumentFold f acc pta callee args =
  foldM foldOverTarget acc (pointsTo pta callee)
  where
    indexedArgs = zip [0..] args
    foldOverTarget a target =
      foldM (f target) a indexedArgs
