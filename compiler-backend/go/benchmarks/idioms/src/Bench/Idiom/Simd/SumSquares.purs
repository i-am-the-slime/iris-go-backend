module Bench.Idiom.Simd.SumSquares where

import Prelude

import Bench.Harness (benchmark)
import Bench.Idiom.Simd.Signal (left)
import Data.Foldable (sum)
import Effect (Effect)

idiom :: String
idiom = "simd: sum of squares, sum (map (\\x -> x * x) xs) over ten million Numbers"

main :: Effect Unit
main = benchmark { size: 0, workload }

workload :: Int -> String
workload _ = show (sum (map (\x -> x * x) left))
