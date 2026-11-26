module Bench.Idiom.Data.MapLookup where

import Prelude

import Bench.Harness (benchmark)
import Bench.Idiom.Random (pseudoRandomArray)
import Data.Array ((..))
import Data.Foldable (foldl)
import Data.Int.Bits (and)
import Data.Map as M
import Data.Maybe (fromMaybe)
import Data.Tuple.Nested ((/\))
import Effect (Effect)

idiom :: String
idiom = "Data.Map Int Int built from sorted pairs, then looked up at pseudo-random keys and folded"

main :: Effect Unit
main = benchmark { size: 2000000, workload }

workload :: Int -> String
workload n = do
  let table = M.fromFoldable ((0 .. 131071) <#> \k -> (k * 2) /\ k)
  let probes = pseudoRandomArray n <#> (_ `and` 0x3FFFF)
  let hits = foldl (\count k -> count + fromMaybe 0 (M.lookup k table)) 0 probes
  show (M.size table) <> " " <> show hits <> " " <> show (foldl (+) 0 table)
