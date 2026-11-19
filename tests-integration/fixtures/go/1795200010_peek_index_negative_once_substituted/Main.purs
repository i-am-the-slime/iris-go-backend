module Main where

import Prelude

import Control.Monad.ST (run)
import Data.Array as Array
import Data.Array.ST as STArray
import Data.Maybe (fromMaybe)

-- The function modify applies is no lambda, so its index is bound to a
-- local when the peek inside modify meets its bounds test, and turns into
-- the constant -1 only once that binding is substituted. Go rejects the
-- read at a constant negative index even in the branch that cannot run.
main :: Array Int
main = run do
  array <- STArray.thaw [ 10, 20, 30 ]
  modified <- STArray.modify (-1) (fromMaybe identity (Array.index [ (_ + 1) ] 20)) array
  kept <- STArray.modify 1 (fromMaybe identity (Array.index [ (_ + 1) ] 0)) array
  elements <- STArray.unsafeFreeze array
  pure (elements <> [ if modified then 1 else 0, if kept then 1 else 0 ])
