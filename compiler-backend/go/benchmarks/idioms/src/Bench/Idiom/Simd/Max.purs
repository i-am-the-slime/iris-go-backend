module Bench.Idiom.Simd.Max where

import Prelude

import Bench.Harness (benchmark)
import Bench.Idiom.Simd.Signal (left)
import Data.Foldable (foldl)
import Data.Number (infinity)
import Effect (Effect)

idiom :: String
idiom = "simd: foldl max (-infinity) over ten million Numbers"

main :: Effect Unit
main = benchmark { size: 0, workload }

workload :: Int -> String
workload _ = show (foldl max (-infinity) left)
