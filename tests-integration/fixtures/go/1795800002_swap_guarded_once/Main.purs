module Main where

import Prelude

import Control.Monad.ST (ST, for, run)
import Data.Array.ST (STArray)
import Data.Array.ST as STArray
import Data.Maybe (fromMaybe)

-- | `peekOrZero` is inlined into `swap`, so the swap's two peeks and two pokes take two bounds
-- | tests, joined into one condition: under it every access is in bounds; outside it each
-- | access tests its own index as before, and an index out of bounds reads zero and writes
-- | nothing.
reversed :: forall region. STArray region Int -> ST region Unit
reversed array = do
  size <- STArray.length array
  for 0 (size / 2) \i -> swap i (size - 1 - i)
  swap 0 size
  swap (-1) 1
  where
  peekOrZero i = map (fromMaybe 0) (STArray.peek i array)

  swap i j = do
    x <- peekOrZero i
    y <- peekOrZero j
    _ <- STArray.poke i y array
    void (STArray.poke j x array)

main :: Array Int
main = run (STArray.withArray reversed [ 1, 2, 3, 4, 5 ])
