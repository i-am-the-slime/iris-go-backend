module Main where

import Prelude

import Data.Int (floor, toNumber)

-- `walk` and `halve` take different parameters, so the loop keeps a variable for each type.
walk :: Int -> Int -> Int
walk steps n
  | n <= 1 = steps
  | n `mod` 2 == 0 = halve (steps + 1) (toNumber n)
  | otherwise = walk (steps + 1) (3 * n + 1)

halve :: Int -> Number -> Int
halve steps x = walk steps (floor (x / 2.0))

isEven :: Int -> Boolean
isEven 0 = true
isEven k = isOdd (k - 1)

isOdd :: Int -> Boolean
isOdd 0 = false
isOdd k = isEven (k - 1)

main :: { steps :: Int, halved :: Int, even :: Boolean }
main = { steps: walk 0 27, halved: halve 0 64.0, even: isEven 100000 }
