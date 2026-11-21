module Bench.Idiom.Simd.IntSum where

import Prelude

import Bench.Harness (benchmark)
import Bench.Idiom.Simd.Signal (counts)
import Data.Foldable (foldl, sum)
import Effect (Effect)

idiom :: String
idiom = "simd: sum and foldl max over ten million Ints"

main :: Effect Unit
main = benchmark { size: 0, workload }

workload :: Int -> String
workload _ = show (sum counts) <> " " <> show (foldl max 0 counts)
