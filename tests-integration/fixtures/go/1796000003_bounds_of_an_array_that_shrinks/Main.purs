module Main where

import Prelude

import Control.Monad.ST (ST, for, run)
import Data.Array.ST (STArray)
import Data.Array.ST as STArray
import Data.Maybe (fromMaybe)

popWhilePeeking :: forall region. STArray region Int -> ST region Unit
popWhilePeeking array = do
  size <- STArray.length array
  for 0 size \i -> do
    x <- map (fromMaybe (-1)) (STArray.peek i array)
    when (x > 2) (void (STArray.pop array))
    void (STArray.poke i (x * 10) array)

growWhilePeeking :: forall region. STArray region Int -> ST region Unit
growWhilePeeking array = do
  size <- STArray.length array
  for 0 (size * 2) \i -> do
    x <- map (fromMaybe 0) (STArray.peek i array)
    void (STArray.push (x + 1) array)

main :: Array Int
main = run (STArray.withArray popWhilePeeking [ 1, 5, 2, 7, 3 ])
  <> run (STArray.withArray growWhilePeeking [ 1, 2 ])
