module Main where

import Prelude

import Data.Array (concatMap, filter, foldl, length, mapWithIndex, (..))

-- A `concatMap` whose callback returns a pipeline runs it as a nested loop,
-- and a literal range is counted rather than built.
main
  :: { pairs :: Array String
     , below :: Int
     , comprehension :: Array Int
     , overRange :: Int
     , indexed :: Array Int
     , materialised :: Array String
     }
main =
  { pairs: concatMap (\x -> map (\y -> show x <> ":" <> show y) (filter (_ > x) numbers)) (filter (_ < 4) numbers)
  , below: length (concatMap (\x -> filter (_ < x) numbers) numbers)
  , comprehension: do
      x <- numbers
      y <- 1 .. 2
      if x > 4 then [ x * y ] else []
  , overRange: foldl (+) 0 (map (_ * 2) (1 .. 10))
  , indexed: mapWithIndex (\i x -> i * 100 + x) (map (_ + 1) numbers)
  , materialised: map show (filter (\x -> x `mod` 2 == 0) (map (_ + 1) numbers))
  }

numbers :: Array Int
numbers = [ 3, 1, 4, 1, 5, 9, 2, 6 ]
