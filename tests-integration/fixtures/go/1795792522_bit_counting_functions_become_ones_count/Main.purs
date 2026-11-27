module Main where

import Prelude

import Data.Int.Bits (zshr, (.&.))



numbers :: Array Int
numbers = [ 0, 1, 2, 3, 255, 256, 1000, 123456789, 2147483647 ]

shiftingCount :: Int -> Int
shiftingCount 0 = 0
shiftingCount number = (number .&. 1) + shiftingCount (number `zshr` 1)

clearingCount :: Int -> Int
clearingCount number
  | number == 0 = 0
  | otherwise = 1 + clearingCount (number .&. (number - 1))

countedFromTheRight :: Int -> Int
countedFromTheRight number = if number == 0 then 0 else countedFromTheRight (number `zshr` 1) + (1 .&. number)

pairsOfBits :: Int -> Int
pairsOfBits 0 = 0
pairsOfBits number = (number .&. 3) + pairsOfBits (number `zshr` 2)

main :: Array (Array Int)
main = [ map shiftingCount numbers, map clearingCount numbers, map countedFromTheRight numbers, map pairsOfBits numbers ]
