module Main where

import Prelude

import Data.Array (head, length, unsafeIndex)
import Data.Foldable (for_)
import Data.Maybe (fromMaybe)
import Effect (Effect)
import Effect.Exception (throw)
import Effect.Ref as Ref
import Partial.Unsafe (unsafePartial)

data Shape = Circle Number | Square Number

area :: Shape -> Number
area = case _ of
  Circle radius -> 3.0 * radius * radius
  Square side -> side * side

sumFrom :: Array Int -> Int -> Int -> Int
sumFrom numbers index total =
  if index >= length numbers then total
  else
    sumFrom numbers (index + 1)
      (total + unsafePartial (unsafeIndex numbers index))

main :: Effect Unit
main = do
  let total = sumFrom [ 1, 2, 3 ] 0 0
  let big = total > 5
  let first = fromMaybe 0 (head [ total ])
  when (first /= 6) do
    throw "the first total is wrong"
  when (total /= 6) do
    throw "the total is wrong"
  areas <- Ref.new 0.0
  for_ [ Circle 1.0, Square 2.0 ] \shape -> do
    Ref.modify_ (_ + area shape) areas
    when big do
      Ref.modify_ (_ + 1.0) areas
  summed <- Ref.read areas
  when (summed /= 9.0) do
    throw "the areas are wrong"
