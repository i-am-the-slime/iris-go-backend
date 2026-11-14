module Bench.Misc.SortBy where

import Prelude

import Bench.Harness (benchmark)
import Data.Array ((..))
import Data.Array as Array
import Data.Ord (comparing)
import Effect (Effect)

hypothesis :: String
hypothesis = "Array.sortBy with a comparator closure on records: JS's FFI merge sort calls the closure through two curried layers, Go calls a specialised func"

main :: Effect Unit
main = benchmark { size: 200000, workload }

workload :: Int -> String
workload n = do
  let records = map (\i -> { key: (i * 7919) `mod` 100003, name: "r" <> show (i `mod` 977) }) (1 .. n)
  let byKey = Array.sortBy (comparing _.key) records
  let byName = Array.sortWith _.name records
  show (map _.key (Array.head byKey)) <> " " <> show (map _.name (Array.last byName)) <> " " <> show (Array.length (Array.nubByEq (\a b -> a.key == b.key) (Array.take 2000 byKey)))
