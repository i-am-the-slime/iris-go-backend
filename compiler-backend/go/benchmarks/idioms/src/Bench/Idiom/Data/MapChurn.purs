module Bench.Idiom.Data.MapChurn where

import Prelude

import Bench.Harness (benchmark)
import Bench.Idiom.Random (pseudoRandomArray)
import Data.Foldable (foldl)
import Data.Int.Bits (and)
import Data.Map as Map
import Data.Maybe (fromMaybe)
import Effect (Effect)

idiom :: String
idiom = "Data.Map Int Int as a frequency table: insertWith on pseudo-random keys, lookup for every key, then foldl over the map"

main :: Effect Unit
main = benchmark { size: 400000, workload }

workload :: Int -> String
workload n = do
  let keys = map (_ `and` 0xFFFF) (pseudoRandomArray n)
  let table = foldl (\m k -> Map.insertWith (+) k 1 m) Map.empty keys
  let hits = foldl (\count k -> count + fromMaybe 0 (Map.lookup k table)) 0 keys
  show (Map.size table) <> " " <> show hits <> " " <> show (foldl (+) 0 table)
