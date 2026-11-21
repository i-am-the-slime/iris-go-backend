module Bench.Idiom.Simd.Mix where

import Prelude

import Bench.Harness (benchmark)
import Bench.Idiom.Simd.Probe (probe)
import Bench.Idiom.Simd.Signal (left, right)
import Data.Array (zipWith)
import Data.Int (toNumber)
import Effect (Effect)

idiom :: String
idiom = "simd: mix two audio buffers with gains and clamp to [-1, 1], zipWith over ten million Numbers"

main :: Effect Unit
main = benchmark { size: 8, workload }

workload :: Int -> String
workload n = do
  let leftGain = toNumber n * 0.1
  let rightGain = 1.0 - leftGain
  probe (zipWith (\l r -> clamp (-1.0) 1.0 (leftGain * l + rightGain * r)) left right)
