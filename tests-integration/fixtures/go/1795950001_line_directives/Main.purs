module Main where

import Prelude

import Data.Array (length, unsafeIndex)
import Effect (Effect)
import Effect.Exception (throw)
import Partial.Unsafe (unsafePartial)

-- | Each statement that calls or indexes names the line it comes from; the
-- | function names the line of its equation.
sumFrom :: Array Int -> Int -> Int -> Int
sumFrom numbers index total =
  if index >= length numbers then total
  else
    sumFrom numbers (index + 1)
      (total + unsafePartial (unsafeIndex numbers index))

main :: Effect Unit
main = do
  let total = sumFrom [ 1, 2, 3 ] 0 0
  when (total /= 6) do
    throw "the total is wrong"
  when (sumFrom [ 4 ] 0 0 /= 4) do
    throw "the second total is wrong"
