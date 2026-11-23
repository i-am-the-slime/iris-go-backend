module Main where

import Prelude

composeTimes :: forall a. (a -> a) -> Int -> a -> a
composeTimes f n = if n <= 0 then identity else f <<< composeTimes f (n - 1)

double :: Int -> Int
double x = x * 2

partiallyApplied :: Array (Int -> Int)
partiallyApplied = [ composeTimes double 2, composeTimes (_ + 3) 2 ]

onlyTheFunction :: Array (Int -> Int -> Int)
onlyTheFunction = [ composeTimes double, composeTimes (_ + 3) ]

main :: Array Int
main =
  [ composeTimes (_ * 2) 5 1
  , composeTimes double 3 7
  , composeTimes (_ + 1) 4 0
  ]
    <> map (\f -> f 1) partiallyApplied
    <> map (\f -> f 3 1) onlyTheFunction
