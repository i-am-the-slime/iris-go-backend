module Bench.Idiom.Simd.Axpy where

import Prelude

import Bench.Harness (benchmark)
import Bench.Idiom.Simd.Probe (probe)
import Bench.Idiom.Simd.Signal (left, right)
import Data.Array (zipWith)
import Data.Int (toNumber)
import Effect (Effect)

idiom :: String
idiom = "simd: axpy, zipWith (\\x y -> a * x + y) over ten million Numbers"

main :: Effect Unit
main = benchmark { size: 3, workload }

workload :: Int -> String
workload n = do
  let a = toNumber n * 0.5
  probe (zipWith (\x y -> a * x + y) left right)
