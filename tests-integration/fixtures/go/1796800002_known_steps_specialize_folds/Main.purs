module Main where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl)

data List a = Nil | Cons a (List a)

foldList :: forall a b. (b -> a -> b) -> b -> List a -> b
foldList step accumulator = case _ of
  Nil -> accumulator
  Cons x rest -> foldList step (step accumulator x) rest

addScaled :: Int -> Int -> Int -> Int
addScaled scale total x = total + scale * x

addSquare :: Int -> Int -> Int
addSquare total x = total + x * x

range :: Int -> Int -> List Int
range low high
  | low > high = Nil
  | otherwise = Cons low (range (low + 1) high)

scaledSum :: Int -> List Int -> Int
scaledSum scale = foldList (addScaled scale) 0

offsetSum :: Int -> List Int -> Int
offsetSum offset = foldList (\total x -> total + x + offset) 0

main :: Array Int
main =
  [ foldList addSquare 0 (range 1 10)
  , foldList (addScaled 3) 0 (range 1 10)
  , scaledSum 5 (range 1 10)
  , scaledSum 7 (range 1 4)
  , offsetSum 100 (range 1 3)
  , foldList max 0 (range 3 9)
  , foldl addSquare 0 (Array.range 1 10)
  , foldl (addScaled 2) 0 (Array.range 1 10)
  ]
