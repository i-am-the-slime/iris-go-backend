module Bench.Recursion.Mutual where

import Prelude

import Bench.Harness (benchmark)
import Data.Array ((..))
import Data.Foldable (foldl)
import Effect (Effect)

hypothesis :: String
hypothesis = "deep mutual tail recursion (isEven/isOdd): unless the backend merges the group into one loop, every step is a call and the stack grows"

main :: Effect Unit
main = benchmark { size: 9000, workload }

workload :: Int -> String
workload n = show (foldl (\count i -> if isEven (5000 + i) then count + 1 else count) 0 (1 .. n))

isEven :: Int -> Boolean
isEven 0 = true
isEven k = isOdd (k - 1)

isOdd :: Int -> Boolean
isOdd 0 = false
isOdd k = isEven (k - 1)
