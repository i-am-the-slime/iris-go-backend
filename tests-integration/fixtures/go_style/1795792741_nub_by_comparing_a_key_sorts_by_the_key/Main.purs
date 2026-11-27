module Main where

import Prelude

import Data.Array as Array
import Data.Ord (comparing)
import Data.Tuple (Tuple(..), fst, snd)
import Effect (Effect)
import Effect.Console (logShow)

numbers :: Array Int
numbers = [ 31, 7, 12, 40, 27, 3, 17, 22, 9, 51 ]

pairs :: Array (Tuple Int Int)
pairs = [ Tuple 1 3, Tuple 2 1, Tuple 3 2, Tuple 4 1 ]

main :: Effect Unit
main = do
  logShow (Array.nubBy (comparing (_ `mod` 10)) numbers)
  logShow (Array.nubBy (comparing snd) pairs)
  logShow (Array.sortBy (comparing snd) pairs)
  logShow (Array.sortBy (comparing (negate <<< fst)) pairs)
