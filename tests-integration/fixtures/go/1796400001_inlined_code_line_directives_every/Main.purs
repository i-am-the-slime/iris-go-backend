module Main where

import Prelude

import Data.Array (length)
import Effect (Effect)
import Effect.Exception (throw)
import Effect.Ref as Ref

twice :: Int -> Int
twice value = value * 2

main :: Effect Unit
main = do
  counter <- Ref.new 3
  total <- Ref.read counter
  let count = total + 1
  let previous = count - 1
  let many = count > 1
  when (twice previous /= 6) do
    throw "twice is wrong"
  when (not many) do
    throw "many is wrong"
  let readings = map (\index -> { value: index * count }) [ total, count ]
  when (show (map (\reading -> twice reading.value) readings) /= "[24,32]") do
    throw "the readings are wrong"
  when (length readings /= 2) do
    throw "the length is wrong"
  Ref.write (twice count) counter
