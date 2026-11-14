module Bench.Exception.EarlyExit where

import Prelude

import Bench.Harness (benchmark)
import Data.Array ((..))
import Data.Array as Array
import Data.Either (Either(..), either)
import Data.Foldable (foldl)
import Data.Maybe (Maybe(..), maybe)
import Data.Traversable (traverse)
import Effect (Effect)

hypothesis :: String
hypothesis = "Maybe and Either early exits through traverse allocate a wrapper per element before failing; JS's young generation absorbs them"

main :: Effect Unit
main = benchmark { size: 3000, workload }

workload :: Int -> String
workload n = do
  let rows = map (\i -> map (\j -> i * 1000 + j) (0 .. 199)) (1 .. n)
  let maybes = foldl (\total row -> total + maybe 0 Array.length (traverse positiveSmall row)) 0 rows
  let eithers = foldl (\total row -> total + either (const 1) Array.length (traverse checked row)) 0 rows
  let found = foldl (\total row -> total + maybe 0 identity (Array.findMap (\x -> if x `mod` 997 == 0 then Just x else Nothing) row)) 0 rows
  show maybes <> " " <> show eithers <> " " <> show found
  where
  positiveSmall x = if x `mod` 1000 < 150 || x < 40000 then Just x else Nothing
  checked x = if x `mod` 1000 == 180 && x > 1500000 then Left x else Right (x * 2)
