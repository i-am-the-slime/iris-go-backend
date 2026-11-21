module Main where

import Prelude

rotate13 :: Int -> Int
rotate13 code =
  if code >= 97 && code <= 122 then 97 + (code - 97 + 13) `mod` 26 else code

digitsAndHalves :: Int -> Int
digitsAndHalves n = go 0 0
  where
  go i total
    | i >= n = total
    | otherwise = go (i + 1) (total + i `mod` 10 + i / 2)

anyInt :: Int -> Int
anyInt x = x `mod` 3 + x / 3

main :: Array Int
main =
  [ rotate13 104, rotate13 122, rotate13 65, digitsAndHalves 25, anyInt (-7), anyInt 7, anyInt (-1) ]
