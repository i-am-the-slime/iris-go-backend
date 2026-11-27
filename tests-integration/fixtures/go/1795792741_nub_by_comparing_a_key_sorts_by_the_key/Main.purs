module Main where

import Prelude

import Data.Array as Array
import Data.Ord (comparing)

numbers :: Array Int
numbers = [ 31, 7, 12, 40, 27, 3, 17, 22, 9, 51 ]

firstOfEachLastDigit :: Array Int -> Array Int
firstOfEachLastDigit = Array.nubBy (comparing (_ `mod` 10))

main :: Array Int
main = firstOfEachLastDigit numbers
