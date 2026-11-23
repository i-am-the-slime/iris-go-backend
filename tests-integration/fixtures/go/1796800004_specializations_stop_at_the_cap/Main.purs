module Main where

import Prelude

iterate :: (Int -> Int) -> Int -> Int -> Int
iterate f count x
  | count <= 0 = x
  | otherwise = iterate f (count - 1) (f x)

plus :: Int -> Int -> Int
plus amount x = x + amount

times :: Int -> Int -> Int
times factor x = x * factor

square :: Int -> Int
square x = x * x

halve :: Int -> Int
halve x = x / 2

main :: Array Int
main =
  [ iterate (plus 1) 3 0
  , iterate (plus 2) 3 0
  , iterate (plus 3) 3 0
  , iterate (times 2) 3 1
  , iterate (times 3) 3 1
  , iterate square 2 3
  , iterate halve 3 100
  , iterate negate 3 5
  , iterate (plus 4) 3 0
  , iterate (times 4) 3 1
  , iterate (plus 1) 5 10
  ]
