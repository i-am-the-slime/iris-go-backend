module Main where

import Prelude

twice :: (Int -> Int) -> Int -> Int
twice f x = f (f x)

nested :: Int -> (Int -> Int) -> Int -> Int
nested depth f x
  | depth <= 0 = f x
  | otherwise = nested (depth - 1) (twice f) x

alternating :: Int -> (Int -> Int -> Int) -> Int -> Int -> Int
alternating depth combine x y
  | depth <= 0 = combine x y
  | otherwise = combine (alternating (depth - 1) (flip combine) y x) depth

increment :: Int -> Int
increment x = x + 1

main :: Array Int
main =
  [ nested 3 increment 0
  , nested 2 (_ * 3) 1
  , alternating 3 sub 10 4
  , alternating 4 (\x y -> x * 10 + y) 1 2
  ]
