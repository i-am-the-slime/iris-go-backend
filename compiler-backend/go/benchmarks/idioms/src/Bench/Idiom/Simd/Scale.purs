module Bench.Idiom.Simd.Scale where

import Prelude

import Bench.Harness (benchmark)
import Bench.Idiom.Simd.Signal (left)
import Bench.Idiom.Simd.Probe (probe)
import Data.Int (toNumber)
import Effect (Effect)

idiom :: String
idiom = "simd: map (_ * k) over ten million Numbers"

main :: Effect Unit
main = benchmark { size: 3, workload }

workload :: Int -> String
workload k = probe (map (_ * toNumber k) left)
