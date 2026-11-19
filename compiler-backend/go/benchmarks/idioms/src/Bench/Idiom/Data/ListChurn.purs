module Bench.Idiom.Data.ListChurn where

import Prelude

import Bench.Harness (benchmark)
import Bench.Idiom.Random (xorshift)
import Data.Foldable (foldl)
import Data.Int.Bits (and)
import Data.List (List(..))
import Data.List as List
import Effect (Effect)

idiom :: String
idiom = "Data.List: build with Cons in a go loop, reverse, filter, map, then foldl, length and head"

main :: Effect Unit
main = benchmark { size: 2000000, workload }

workload :: Int -> String
workload n = do
  let reversed = List.reverse (build n)
  let evens = List.filter (\x -> x `and` 1 == 0) reversed
  show (List.length evens) <> " " <> show (foldl (+) 0 (map (_ * 3) evens)) <> " " <> show (List.head reversed)

build :: Int -> List Int
build n = go 0 Nil
  where
  go i acc
    | i >= n = acc
    | otherwise = go (i + 1) (Cons (xorshift (i + 1)) acc)
