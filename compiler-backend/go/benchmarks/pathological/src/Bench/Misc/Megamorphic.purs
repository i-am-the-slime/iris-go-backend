module Bench.Misc.Megamorphic where

import Prelude

import Bench.Harness (benchmark)
import Data.Array ((..))
import Data.Array as Array
import Data.Foldable (foldl)
import Data.Maybe (fromMaybe)
import Effect (Effect)

hypothesis :: String
hypothesis = "one higher-order call site receives 16 different closures in rotation; it is megamorphic in JS too, so Go's indirect calls should hold up"

type Shape = { area :: Int -> Int, scale :: Int -> Int -> Int, name :: String }

main :: Effect Unit
main = benchmark { size: 2000000, workload }

workload :: Int -> String
workload n = do
  let shapes = map shape (0 .. 15)
  let total = foldl (\accumulated i -> apply' (pick shapes i) i accumulated) 0 (1 .. n)
  show total
  where
  apply' shape i accumulated = (accumulated + shape.area i + shape.scale i 3) `mod` 1000003
  pick shapes i = fromMaybe (shape 0) (Array.index shapes (i `mod` 16))

shape :: Int -> Shape
shape k = case k `mod` 8 of
  0 -> { area: \i -> i * k, scale: \i s -> i * s, name: "a" }
  1 -> { area: \i -> i + k, scale: \i s -> i - s, name: "b" }
  2 -> { area: \i -> i `mod` (k + 1), scale: \_ s -> s, name: "c" }
  3 -> { area: \_ -> k, scale: \i s -> (i * s) `mod` 7, name: "d" }
  4 -> { area: \i -> i * i `mod` 101, scale: \i _ -> i, name: "e" }
  5 -> { area: \i -> if i > k then 1 else 0, scale: \i s -> max i s, name: "f" }
  6 -> { area: \i -> negate i, scale: \i s -> min i s, name: "g" }
  _ -> { area: \i -> i / (k + 1), scale: \i s -> i + s + k, name: "h" }
