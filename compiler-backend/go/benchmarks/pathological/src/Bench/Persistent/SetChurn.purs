module Bench.Persistent.SetChurn where

import Prelude

import Bench.Harness (benchmark)
import Data.Array ((..))
import Data.Foldable (foldl)
import Data.Set as Set
import Effect (Effect)

hypothesis :: String
hypothesis = "Data.Set insert, delete, member and union allocate small tree nodes per operation"

main :: Effect Unit
main = benchmark { size: 150000, workload }

workload :: Int -> String
workload n = do
  let evens = foldl (\set i -> Set.insert (i * 2 `mod` 70001) set) Set.empty (1 .. n)
  let thirds = foldl (\set i -> Set.insert (i * 3 `mod` 70001) set) Set.empty (1 .. n)
  let pruned = foldl (\set i -> if Set.member i thirds then Set.delete i set else set) evens (1 .. n)
  let joined = Set.union pruned thirds
  show (Set.size evens) <> " " <> show (Set.size pruned) <> " " <> show (Set.size joined) <> " " <> show (Set.size (Set.intersection evens thirds))
