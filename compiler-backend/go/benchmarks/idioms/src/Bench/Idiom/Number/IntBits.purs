module Bench.Idiom.Number.IntBits where

import Prelude

import Bench.Harness (benchmark)
import Bench.Idiom.Random (xorshift)
import Data.Int.Bits (and, zshr)
import Effect (Effect)

idiom :: String
idiom = "Data.Int.Bits in tail-recursive loops: xorshift steps with shl, zshr and xor, then a popcount with and and zshr per step"

main :: Effect Unit
main = benchmark { size: 3000000, workload }

workload :: Int -> String
workload n = show (go 0 88172645 0)
  where
  go i seed acc
    | i >= n = acc
    | otherwise = do
        let next = xorshift seed
        go (i + 1) next (acc + popCount next)

popCount :: Int -> Int
popCount x = go x 0
  where
  go 0 acc = acc
  go v acc = go (v `zshr` 1) (acc + (v `and` 1))
