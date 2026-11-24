module Main where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Int64 (Int64)
import Data.Int64 as Int64
import Data.UInt64 (UInt64)
import Data.UInt64 as UInt64

-- | purescript-int64 orders its Longs by the three-way `compare_`, whose cases are Go's own
-- | comparisons of int64 and uint64: `max` and `min` choose by one of them, and their folds run
-- | as vector lanes like Int's.
largest :: Array Int64 -> Int64
largest xs = foldl max bottom xs

smallest :: Array UInt64 -> UInt64
smallest xs = foldl min top xs

largestInt :: Array Int -> Int
largestInt xs = foldl max bottom xs

largestNumber :: Array Number -> Number
largestNumber xs = foldl max 0.0 xs

-- | `<`, `<=` and a case of `compare` test the outcomes they care for with one comparison each.
below :: Int64 -> Array Int64 -> Array Int64
below pivot xs = Array.filter (\x -> x < pivot) xs

notAbove :: UInt64 -> Array UInt64 -> Array UInt64
notAbove pivot xs = Array.filter (\x -> x <= pivot) xs

orderings :: Int64 -> Array Int64 -> Array Int
orderings pivot xs = map ordering xs
  where
  ordering x = case compare x pivot of
    LT -> 1
    EQ -> 2
    GT -> 3

-- | Comparing constants is decided at compile time.
constant :: Boolean
constant = Int64.fromInt 1 < Int64.fromInt 2 && UInt64.unsafeFromInt (-1) > UInt64.unsafeFromInt 1

main :: Array String
main = do
  let ints = [ 3, -1, 4, 1, -5, 9, 2, 6, 5, 3, -5, 8, 9, 7, 9, 3, 2, 3, 8, 4, -6, 2, 6, 4, 3, 3, 8, 3, 2, 7, 9, 5, 0 ]
  let xs = map Int64.fromInt ints
  let us = map UInt64.unsafeFromInt ints
  let numbers = [ 3.5, -1.0, 4.0, 1.0, -5.0, 9.25, 2.0, 6.0, 5.0, 3.0, -5.0, 8.0, 9.0, 7.0, 9.0, 3.0, 2.0, 3.0, 8.0, 4.0, -6.0, 2.0, 6.0, 4.0, 3.0, 3.0, 8.0, 3.0, 2.0, 7.0, 9.0, 5.0, 0.0 ]
  [ show (largest xs), show (smallest us), show (largestInt ints), show (largestNumber numbers)
  , show (below (Int64.fromInt 2) xs), show (notAbove (UInt64.unsafeFromInt 2) us), show (orderings (Int64.fromInt 3) xs)
  , show constant
  ]
