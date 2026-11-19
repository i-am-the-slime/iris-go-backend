module Bench.Idiom.Pure.GoLoops where

import Prelude

import Bench.Harness (benchmark)
import Bench.Idiom.Random (pseudoRandomArray)
import Data.Array as Array
import Data.Foldable (foldl)
import Data.Int.Bits (and)
import Data.Maybe (fromMaybe)
import Effect (Effect)
import Partial.Unsafe (unsafePartial)

idiom :: String
idiom = "pure loops: a tail-recursive go with Int accumulators, foldl over an array, index and unsafeIndex in go loops, and foldl over map over range"

main :: Effect Unit
main = benchmark { size: 3000000, workload }

workload :: Int -> String
workload n = do
  let xs = pseudoRandomArray n
  show (digitSums n)
    <> " " <> show (foldl (+) 0 xs)
    <> " " <> show (indexedSum xs)
    <> " " <> show (unsafeIndexedSum xs)
    <> " " <> show (fusedSum n)

digitSums :: Int -> Int
digitSums n = go 1 0
  where
  go i acc
    | i > n = acc
    | otherwise = go (i + 1) (acc + digitSum i 0)

  digitSum x acc
    | x == 0 = acc
    | otherwise = digitSum (x / 10) (acc + x `mod` 10)

indexedSum :: Array Int -> Int
indexedSum xs = go 0 0
  where
  size = Array.length xs

  go i acc
    | i >= size = acc
    | otherwise = go (i + 1) (acc + fromMaybe 0 (Array.index xs i))

unsafeIndexedSum :: Array Int -> Int
unsafeIndexedSum xs = go 0 0
  where
  size = Array.length xs

  go i acc
    | i >= size = acc
    | otherwise = go (i + 1) (acc + unsafePartial (Array.unsafeIndex xs i))

fusedSum :: Int -> Int
fusedSum n = foldl (+) 0 (map (_ `and` 1023) (Array.range 1 n))
