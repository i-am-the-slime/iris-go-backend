module Main where

import Prelude

import Control.Monad.ST (ST, for, run)
import Data.Array as Array
import Data.Array.ST (STArray)
import Data.Array.ST as STArray
import Data.Maybe (fromMaybe)

doubleEach :: forall region. STArray region Int -> ST region Unit
doubleEach array = do
  size <- STArray.length array
  for 0 size \i -> do
    x <- map (fromMaybe 0) (STArray.peek i array)
    void (STArray.poke i (x * 2) array)

shiftLeftFromOne :: forall region. STArray region Int -> ST region Unit
shiftLeftFromOne array = do
  size <- STArray.length array
  for 1 size \i -> do
    x <- map (fromMaybe 0) (STArray.peek i array)
    void (STArray.poke (i - 1) x array)

sumByIndex :: Array Int -> Int
sumByIndex xs = go 0 0
  where
  size = Array.length xs

  go i total
    | i >= size = total
    | otherwise = go (i + 1) (total + fromMaybe 0 (Array.index xs i))

main :: Array Int
main = do
  let doubled = run (STArray.withArray doubleEach [ 1, 2, 3 ])
  let shifted = run (STArray.withArray shiftLeftFromOne [ 4, 5, 6 ])
  doubled <> shifted <> [ sumByIndex doubled ]
