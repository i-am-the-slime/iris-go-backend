module Bench.Idiom.Data.BTreeChurn where

import Prelude

import Bench.Harness (benchmark)
import Bench.Idiom.Random (pseudoRandomArray)
import Data.BTreeMap as BTree
import Data.Foldable (foldl)
import Data.Int.Bits (and)
import Data.Maybe (fromMaybe)
import Effect (Effect)

idiom :: String
idiom = "Data.MapChurn on a PureScript B-tree: insertWith on pseudo-random keys, lookup for every key, then foldl over the map"

main :: Effect Unit
main = benchmark { size: 400000, workload }

workload :: Int -> String
workload n = do
  let keys = pseudoRandomArray n <#> (_ `and` 0xFFFF)
  let table = foldl (\m k -> BTree.insertWith (+) k 1 m) BTree.empty keys
  let hits = foldl (\count k -> count + fromMaybe 0 (BTree.lookup k table)) 0 keys
  show (BTree.size table) <> " " <> show hits <> " " <> show (foldl (+) 0 table)
