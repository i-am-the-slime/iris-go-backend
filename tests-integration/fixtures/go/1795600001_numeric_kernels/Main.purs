module Main where

import Prelude

import Data.Array (zipWith)
import Data.Foldable (foldl, sum)
import Data.Number (infinity)

-- | Sums, products and maxima of Numbers and Ints fold as vector lanes.
total :: Array Number -> Number
total xs = foldl (+) 0.0 xs

dot :: Array Number -> Array Number -> Number
dot xs ys = sum (zipWith (*) xs ys)

sumOfSquares :: Array Number -> Number
sumOfSquares xs = sum (map (\x -> x * x) xs)

largest :: Array Number -> Number
largest xs = foldl max (-infinity) xs

product :: Array Int -> Int
product xs = foldl (*) 1 xs

smallestInt :: Array Int -> Int
smallestInt xs = foldl min top xs

-- | Maps and zipWiths of arithmetic, comparisons and captured scalars store whole vectors.
axpy :: Number -> Array Number -> Array Number -> Array Number
axpy a xs ys = zipWith (\x y -> a * x + y) xs ys

mix :: Number -> Array Number -> Array Number -> Array Number
mix gain left right = zipWith (\l r -> clamp (-1.0) 1.0 (gain * l + (1.0 - gain) * r)) left right

-- | `Data.Ord.min` keeps a NaN element, so its Number fold depends on order and stays scalar.
smallest :: Array Number -> Number
smallest xs = foldl min infinity xs

-- | A fold that is not a reduction stays scalar.
decayed :: Array Number -> Number
decayed xs = foldl (\acc x -> acc * 0.5 + x) 0.0 xs

-- | Short literal arrays stay scalar.
literal :: Int
literal = foldl (+) 0 [ 1, 2, 3 ]

main :: Array String
main = do
  let xs = map (\i -> 0.25 * i) [ 1.0, -2.0, 3.0, 4.0, -5.0, 6.0, 7.0, 8.0, 9.0, -10.0, 11.0, 12.0, 13.0, 14.0, 15.0, 16.0, 17.0, 18.0, 19.0, -20.0, 21.0, 22.0, 23.0, 24.0, 25.0, 26.0, 27.0, 28.0, 29.0, 30.0, 31.0, 32.0, 33.0, 34.0, 35.0 ]
  let ints = map (_ - 7) [ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33 ]
  [ show (total xs), show (dot xs xs), show (sumOfSquares xs), show (largest xs), show (product ints)
  , show (smallestInt ints), show (axpy 2.0 xs xs), show (mix 0.75 xs xs), show (smallest xs)
  , show (decayed xs), show literal
  ]
