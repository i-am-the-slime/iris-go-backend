module Bench.Idiom.Simd.Sum where

import Prelude

import Bench.Harness (benchmark)
import Bench.Idiom.Simd.Signal (left)
import Data.Foldable (foldl)
import Effect (Effect)

idiom :: String
idiom = "simd: foldl (+) 0.0 over ten million Numbers"

main :: Effect Unit
main = benchmark { size: 0, workload }

workload :: Int -> String
workload _ = show (foldl (+) 0.0 left)
