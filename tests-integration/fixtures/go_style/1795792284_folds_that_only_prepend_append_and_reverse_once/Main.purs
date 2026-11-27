module Main where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl, foldr)
import Effect (Effect)
import Effect.Console (logShow)

numbers :: Array Int
numbers = Array.range 1 5

reversedByConsing :: Array Int -> Array Int
reversedByConsing = foldl (flip Array.cons) []

evenPairsInFrontOfASeed :: Array Int -> Array Int
evenPairsInFrontOfASeed = foldl prependEvenPair [ 100 ]
  where
  prependEvenPair kept number
    | number `mod` 2 == 0 = [ number, number * 10 ] <> kept
    | otherwise = kept

doubledFromTheRight :: Array Int -> Array Int
doubledFromTheRight = foldr (\number kept -> Array.cons (number * 2) kept) []

lengthsSoFar :: Array Int -> Array Int
lengthsSoFar = foldl (\kept _ -> Array.cons (Array.length kept) kept) []

main :: Effect Unit
main = do
  logShow (reversedByConsing numbers)
  logShow (evenPairsInFrontOfASeed numbers)
  logShow (doubledFromTheRight numbers)
  logShow (lengthsSoFar numbers)
  logShow (reversedByConsing [])
