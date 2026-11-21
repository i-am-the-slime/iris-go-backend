module Main where

import Prelude

import Control.Monad.ST (ST, for, run)
import Data.Array.ST (STArray)
import Data.Array.ST as STArray
import Data.Maybe (fromMaybe)

peekOrZero :: forall region. Int -> STArray region Int -> ST region Int
peekOrZero i array = map (fromMaybe 0) (STArray.peek i array)

onePastTheEnd :: forall region. STArray region Int -> ST region Unit
onePastTheEnd array = do
  size <- STArray.length array
  for 0 (size + 1) \i -> do
    x <- peekOrZero i array
    void (STArray.poke i (x + 1) array)

oneBeforeTheStart :: forall region. STArray region Int -> ST region Unit
oneBeforeTheStart array = do
  size <- STArray.length array
  for 0 size \i -> do
    previous <- peekOrZero (i - 1) array
    void (STArray.modify i (_ + previous) array)

main :: Array Int
main = run (STArray.withArray onePastTheEnd [ 1, 2, 3 ])
  <> run (STArray.withArray oneBeforeTheStart [ 1, 2, 3 ])
