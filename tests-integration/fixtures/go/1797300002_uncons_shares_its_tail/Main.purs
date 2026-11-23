module Main where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Effect (Effect)

summed :: Int -> Array Int -> Int
summed total remaining = case Array.uncons remaining of
  Just { head, tail } -> summed (total + head) tail
  Nothing -> total

firstAndRest :: Array Int -> Int
firstAndRest numbers = case Array.uncons numbers of
  Just { head, tail } -> head * 100 + Array.length tail
  Nothing -> -1

main :: Effect Int
main = pure (summed 0 [ 1, 2, 3 ] + firstAndRest [ 4, 5 ] + firstAndRest [])
