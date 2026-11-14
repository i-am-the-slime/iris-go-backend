module Bench.Record.WideUpdate where

import Prelude

import Bench.Harness (benchmark)
import Effect (Effect)

hypothesis :: String
hypothesis = "updating one field of a 20-field record copies all 20 fields; V8 clones a known hidden class with a fast path"

type Wide =
  { f01 :: Int, f02 :: Int, f03 :: Int, f04 :: Int, f05 :: Int
  , f06 :: Int, f07 :: Int, f08 :: Int, f09 :: Int, f10 :: Int
  , f11 :: Int, f12 :: Int, f13 :: Int, f14 :: Int, f15 :: Int
  , f16 :: Int, f17 :: Int, f18 :: Int, f19 :: Int, f20 :: Int
  }

main :: Effect Unit
main = benchmark { size: 3000000, workload }

workload :: Int -> String
workload n = do
  let final = loop 0 initial
  show (final.f01 + final.f07 + final.f13 + final.f20)
  where
  loop i wide
    | i >= n = wide
    | otherwise = loop (i + 1) (update i wide)

  update i wide = case i `mod` 4 of
    0 -> wide { f01 = wide.f01 + 1 }
    1 -> wide { f07 = wide.f07 + i `mod` 3 }
    2 -> wide { f13 = wide.f13 - 1 }
    _ -> wide { f20 = wide.f20 + wide.f01 `mod` 5 }

initial :: Wide
initial =
  { f01: 1, f02: 2, f03: 3, f04: 4, f05: 5, f06: 6, f07: 7, f08: 8, f09: 9, f10: 10
  , f11: 11, f12: 12, f13: 13, f14: 14, f15: 15, f16: 16, f17: 17, f18: 18, f19: 19, f20: 20
  }
