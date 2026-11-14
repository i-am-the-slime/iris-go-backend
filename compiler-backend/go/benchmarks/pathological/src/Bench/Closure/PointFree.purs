module Bench.Closure.PointFree where

import Prelude

import Bench.Harness (benchmark)
import Data.Array ((..))
import Data.Array as Array
import Data.Foldable (foldl, foldr)
import Data.Function (applyN)
import Effect (Effect)

hypothesis :: String
hypothesis = "point-free pipelines build composed and partially applied closures at runtime; V8 inlines through them, Go calls each indirectly"

main :: Effect Unit
main = benchmark { size: 300000, workload }

workload :: Int -> String
workload n = do
  let numbers = 1 .. n
  let stages = map stage (0 .. 15)
  let composed = foldr (>>>) identity stages
  let mapped = map composed numbers
  let filtered = Array.filter (eq 0 <<< flip mod 3) mapped
  let folded = foldl (flip (add <<< flip mod 1000)) 0 filtered
  let repeated = foldl (\total i -> total + applyN (add 3 >>> mul 2 >>> flip mod 1009) (i `mod` 8) i) 0 numbers
  show folded <> " " <> show repeated <> " " <> show (Array.length filtered)
  where
  stage :: Int -> Int -> Int
  stage k = case k `mod` 4 of
    0 -> add k
    1 -> flip mod (1000 + k)
    2 -> mul 3 >>> sub k
    _ -> clampTo k
  clampTo k = clamp (negate k) (100000 + k)
