module Bench.Lazy.ListStream where

import Prelude

import Bench.Harness (benchmark)
import Data.Foldable (foldl)
import Data.List.Lazy as LazyList
import Effect (Effect)

hypothesis :: String
hypothesis = "an infinite Data.List.Lazy stream (take n of filter of iterate) allocates a Lazy cell and closure per element"

main :: Effect Unit
main = benchmark { size: 200000, workload }

workload :: Int -> String
workload n = do
  let collatz = LazyList.iterate (\x -> if x `mod` 2 == 0 then x / 2 else (3 * x + 1) `mod` 1000003) 27
  let odds = LazyList.take n (LazyList.filter (\x -> x `mod` 2 == 1) collatz)
  let zipped = LazyList.take n (LazyList.zipWith (+) odds (LazyList.iterate (_ + 1) 0))
  show (foldl (+) 0 odds) <> " " <> show (foldl (\total x -> (total + x) `mod` 1000003) 0 zipped)
