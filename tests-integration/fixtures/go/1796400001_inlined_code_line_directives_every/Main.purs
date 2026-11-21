module Main where

import Prelude

import Data.Array (length)
import Data.Int (toNumber)
import Effect (Effect)
import Effect.Exception (throw)
import Effect.Ref as Ref

data Shape
  = Circle Number
  | Rectangle Number Number
  | Dot

data Colour = Red | Green

derive instance Eq Colour

twice :: Int -> Int
twice value = value * 2

area :: Shape -> Number
area = case _ of
  Circle radius -> 3.0 * radius * radius
  Rectangle width height -> width * height
  Dot -> 0.0

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
  let shapes = [ Circle (toNumber total), Rectangle 2.0 (toNumber count), Dot ]
  when (map area shapes /= [ 27.0, 8.0, 0.0 ]) do
    throw "the areas are wrong"
  colours <- Ref.new [ Green ]
  Ref.modify_ (\pending -> pending <> [ if many then Red else Green ]) colours
  painted <- Ref.read colours
  when (painted /= [ Green, Red ]) do
    throw "the colour is wrong"
  Ref.write (twice count) counter
