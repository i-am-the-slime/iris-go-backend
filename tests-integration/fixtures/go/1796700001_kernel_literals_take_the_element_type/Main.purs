module Main where

import Prelude

import Data.Array (drop, zipWith)
import Data.Foldable (sum)

-- | Literals a kernel's scalar loop selects or binds are of the element's Go type.
ascents :: Array Int -> Int
ascents xs = sum (zipWith (\x y -> if x > y then 1 else 0) xs (drop 1 xs))

ascentsNumber :: Array Number -> Number
ascentsNumber xs = sum (zipWith (\x y -> if x > y then 1.0 else 0.0) xs (drop 1 xs))

signs :: Array Int -> Int
signs xs = sum (map (\x -> if x < 0 then -1 else 2) xs)

sign :: Int -> Int
sign x = if x < 0 then -1 else if x > 0 then 1 else 0

signum :: Array Int -> Int
signum xs = sum (map sign xs)

drops :: Array Int -> Array Int
drops xs = zipWith (\x y -> if x > y then x - y else 0) xs (drop 1 xs)

totalDrop :: Array Int -> Int
totalDrop xs = sum (zipWith (\x y -> if x > y then x - y else 0) xs (drop 1 xs))

main :: Array String
main = do
  let ints = map (\i -> (i * 37) `mod` 11 - 5) [ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37 ]
  let numbers = map (\i -> 0.5 * i) [ 3.0, -1.0, 4.0, 1.0, -5.0, 9.0, 2.0, 6.0, -5.0, 3.0, 5.0, 8.0, 9.0, -7.0, 9.0, 3.0, 2.0, 3.0, -8.0, 4.0, 6.0, 2.0, 6.0, 4.0, -3.0, 3.0, 8.0, 3.0, 2.0, 7.0, 9.0, 5.0, 0.0, 2.0, 8.0, 8.0, 4.0 ]
  [ show (ascents ints), show (ascentsNumber numbers), show (signs ints), show (signum ints)
  , show (drops ints), show (totalDrop ints)
  ]
