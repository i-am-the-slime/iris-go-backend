module Bench.List.Strict where

import Prelude

import Bench.Harness (benchmark)
import Data.Array ((..))
import Data.Foldable (foldl, sum)
import Data.List as List
import Effect (Effect)

hypothesis :: String
hypothesis = "strict Data.List map, filter, reverse, sort and nub allocate a cons cell per element per pass"

main :: Effect Unit
main = benchmark { size: 40000, workload }

workload :: Int -> String
workload n = show (foldl (\total round -> total + pass round) 0 (1 .. (n / 4000)))
  where
  pass round = do
    let list = List.fromFoldable (round .. (round + 4000))
    let mapped = map (\x -> (x * 7919) `mod` 10007) list
    let filtered = List.filter (\x -> x `mod` 3 /= 0) mapped
    let sorted = List.sort filtered
    let unique = List.nub (map (_ `mod` 500) sorted)
    (sum sorted + List.length unique + foldl (+) 0 (List.reverse (List.take 100 sorted))) `mod` 1000003
