module Bench.Idiom.Simd.Dot where

import Prelude

import Bench.Harness (benchmark)
import Bench.Idiom.Simd.Signal (left, right)
import Data.Array (zipWith)
import Data.Foldable (sum)
import Effect (Effect)

idiom :: String
idiom = "simd: dot product, sum (zipWith (*) xs ys) over ten million Numbers"

main :: Effect Unit
main = benchmark { size: 0, workload }

workload :: Int -> String
workload _ = show (sum (zipWith (*) left right))
