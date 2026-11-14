module Bench.Persistent.MapChurn where

import Prelude

import Bench.Harness (benchmark)
import Data.Array ((..))
import Data.Foldable (foldl)
import Data.Map as Map
import Data.Maybe (fromMaybe)
import Effect (Effect)

hypothesis :: String
hypothesis = "Data.Map insert, delete and lookup allocate a fresh path of small nodes per operation, which a young generation reclaims cheaply"

main :: Effect Unit
main = benchmark { size: 200000, workload }

workload :: Int -> String
workload n = do
  let final = foldl churn Map.empty (1 .. n)
  show (Map.size final) <> " " <> show (Map.lookup 4242 final) <> " " <> show (foldl (+) 0 final)
  where
  churn map i = do
    let key = (i * 7919) `mod` 50021
    let inserted = Map.insert key i map
    let deleted = Map.delete ((key * 13) `mod` 50021) inserted
    Map.insert (key + 1) (fromMaybe 0 (Map.lookup key deleted) + 1) deleted
