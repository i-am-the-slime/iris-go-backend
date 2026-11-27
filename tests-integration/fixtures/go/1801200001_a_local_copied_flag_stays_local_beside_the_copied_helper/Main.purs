module Main where

import Prelude

import Control.Monad.ST as ST
import Data.Array as Array
import Data.Array.ST as STArray
import Data.Foldable (foldl)
import Data.Maybe (fromMaybe)
import Effect (Effect)
import Journal (log, positions)

-- | Emitted first, with a local flag `copied` for its one copy of `values`.
overwriteEach :: Array Int -> Array Int -> Array Int
overwriteEach values positions = foldl overwrite values positions
  where
  overwrite current position = fromMaybe current (Array.updateAt position (position * 3) current)

-- | Emitted later, freezing through the support function named `copied` too.
pushedCopies :: Int -> Array Int -> Array Int
pushedCopies times values
  | times <= 0 = values
  | otherwise = pushedCopies (times - 1) (ST.run (STArray.thaw values >>= \cells -> STArray.push times cells *> STArray.freeze cells))

main :: Effect Unit
main = do
  log (show (overwriteEach [ 1, 2, 3, 4 ] positions))
  log (show (overwriteEach [ 5, 6, 7 ] positions))
  log (show (pushedCopies 3 positions))
