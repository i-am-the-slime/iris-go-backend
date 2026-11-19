module Bench.Idiom.Data.SmallADT where

import Prelude

import Bench.Harness (benchmark)
import Data.Array as Array
import Data.Foldable (foldl)
import Data.Int.Bits (and, shr)
import Data.Maybe (Maybe(..))
import Effect (Effect)

idiom :: String
idiom = "a small ADT constructed and matched on every step of a fold over a range, plus a Maybe from Array.index per step"

main :: Effect Unit
main = benchmark { size: 5000000, workload }

data Shape = Circle Int | Square Int | Rectangle Int Int

workload :: Int -> String
workload n = do
  let sides = Array.range 1 64
  show (foldl (\total i -> total + area (shape sides i)) 0 (Array.range 1 n))

shape :: Array Int -> Int -> Shape
shape sides i = case i `mod` 3 of
  0 -> Circle (i `and` 15)
  1 -> Square (side (i `and` 63))
  _ -> Rectangle (i `and` 15) ((i `shr` 4) `and` 15)
  where
  side index = case Array.index sides index of
    Just s -> s
    Nothing -> 1

area :: Shape -> Int
area = case _ of
  Circle r -> 3 * r * r
  Square s -> s * s
  Rectangle w h -> w * h
