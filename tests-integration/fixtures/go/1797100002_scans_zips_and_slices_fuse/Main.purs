module Main where

import Prelude

import Data.Array as Array
import Data.Foldable (all, any, foldl, foldr, sum)
import Data.Int.Bits (shl, xor, zshr)
import Data.String.CodeUnits (toCharArray)

next :: Int -> Int
next x0 = do
  let x1 = x0 `xor` (x0 `shl` 13)
  let x2 = x1 `xor` (x1 `zshr` 17)
  x2 `xor` (x2 `shl` 5)

stream :: Int -> Int -> Int -> Array Int
stream seed count bound = Array.scanl (\state _ -> next state) seed (Array.replicate count unit) <#> \state -> (state `zshr` 1) `mod` bound

runningSums :: Array Int -> Array Int
runningSums = Array.scanl (+) 0

row :: Array Char -> Array Int -> Char -> Array Int
row letters previous letter =
  Array.scanl (\left cheapest -> min (left + 1) cheapest) first (Array.zipWith min deleting replacing)
    # Array.cons first
  where
  first = sum (Array.take 1 previous) + 1
  deleting = Array.drop 1 previous <#> (_ + 1)
  replacing = Array.zipWith (\diagonal other -> diagonal + if other == letter then 0 else 1) previous letters

distance :: String -> String -> Int
distance source target = sum (Array.drop (Array.length letters) (foldl (row letters) (Array.range 0 (Array.length letters)) (toLetters source)))
  where
  letters = toCharArray target
  toLetters = toCharArray

type Run = { matches :: Int, before :: Int, total :: Int }

countAlong :: Array Boolean -> Int
countAlong matches = (foldl step { matches: 0, before: 0, total: 0 } matches).total
  where
  step run same
    | same = run { matches = run.matches + 1, total = run.total + run.before }
    | otherwise = do
        let starts = run.matches + 1
        { matches: 0, before: starts, total: run.total + starts }

differences :: Array Int -> Array Int -> Int
differences xs ys = sum (Array.range 0 (Array.length xs - 1) <#> \start -> countAlong (Array.zipWith (==) (Array.drop start xs) ys))

unshared :: Array Int -> Int
unshared xs = (foldl step { low: 0, high: 0 } xs).high
  where
  step bounds x
    | x < 3 = bounds { low = bounds.low + x, high = bounds.high + bounds.low }
    | otherwise = { low: bounds.low - 1, high: bounds.high + x }

main :: Array String
main =
  [ show (stream 7 12 100)
  , show (stream 7 0 100)
  , show (stream 7 (-3) 100)
  , show (runningSums [ 3, 1, 4, 1, 5 ])
  , show (runningSums [])
  , show (Array.scanl (+) 10 (Array.filter (_ > 1) [ 3, 1, 4, 1, 5 ] <#> (_ * 2)))
  , show (Array.scanl (\acc x -> acc * 2 + x) 1 (Array.range 3 (-2)))
  , show (foldl (+) 0 (Array.scanl (+) 0 (Array.range 1 100)))
  , show (foldr (\x acc -> x - acc) 0 (Array.scanl (+) 0 [ 1, 2, 3, 4 ]))
  , show (Array.length (Array.scanl (+) 0 [ 1, 2, 3 ]))
  , show (any (_ > 6) (Array.scanl (+) 0 [ 1, 2, 3, 4 ]))
  , show (all (_ < 6) (Array.scanl (+) 0 [ 1, 2, 3, 4 ]))
  , show (Array.filter (\x -> x `mod` 2 == 0) (Array.scanl (+) 0 [ 1, 2, 3, 4, 5 ]))
  , show (Array.concatMap (\n -> Array.scanl (+) n [ 1, 1, 1 ]) [ 10, 20 ])
  , show (Array.zipWith (+) [ 1, 2, 3, 4 ] [ 10, 20 ])
  , show (Array.zipWith (+) [] [ 10, 20 ])
  , show (Array.zipWith (\x y -> { x, y }) (Array.drop 2 [ 1, 2, 3, 4, 5 ]) (Array.range 7 3))
  , show (Array.zipWith (-) (Array.slice (-3) (-1) [ 1, 2, 3, 4, 5 ]) (Array.slice 1 100 [ 10, 20, 30 ]))
  , show (Array.zipWith (*) (Array.slice 4 2 [ 1, 2, 3, 4, 5 ]) [ 1, 2 ])
  , show (Array.zipWith (*) (Array.drop (-2) [ 1, 2, 3 ]) (Array.drop 9 [ 1, 2, 3 ]))
  , show (sum (Array.zipWith (*) (Array.mapWithIndex (\i x -> i * x) [ 5, 6, 7 ]) (Array.replicate 5 3)))
  , show (Array.zipWith (+) (Array.zipWith (*) [ 1, 2, 3 ] [ 4, 5, 6 ]) (Array.scanl (+) 0 [ 1, 1, 1, 1 ]))
  , show (Array.mapWithIndex (\i x -> i + x) (Array.zipWith (+) [ 1, 2, 3 ] [ 4, 5, 6 ]))
  , show (Array.length (Array.zipWith (+) [ 1, 2, 3 ] (Array.drop 1 [ 4, 5, 6 ])))
  , show (all identity (Array.zipWith (<) [ 1, 2, 3 ] [ 2, 3, 1 ]))
  , show (Array.replicate 3 { name: "r" } <#> _.name)
  , show (foldl (+) 0 (Array.replicate 4 5))
  , show (Array.cons 0 (Array.scanl (+) 1 [ 1, 2, 3 ]))
  , show (Array.cons 0 (Array.filter (_ > 1) [ 1, 2, 3 ]))
  , show ([ 7, 8 ] <> map (_ * 3) [ 1, 2 ])
  , show (Array.cons 0 (Array.concatMap (\x -> [ x, x ]) [ 1, 2 ]))
  , show (row [ 'a', 'b' ] [ 0, 1, 2 ] 'b')
  , show (distance "abcab" "bca")
  , show (differences [ 1, 2, 1, 1 ] [ 2, 1, 1 ])
  , show (countAlong [ true, false, true, true, false ])
  , show (unshared [ 1, 5, 2, 7, 0 ])
  ]
