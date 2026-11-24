module Main where

import Prelude

import Data.Array (filter, length, (..))
import Data.Foldable (foldl, sum)
import Data.Int (toNumber)

shortLiteralStaysScalar :: Int
shortLiteralStaysScalar = sum (map (_ * 2) [ 1, 2, 3 ])

shortRangeStaysScalar :: Array Int
shortRangeStaysScalar = map (_ * 3) (1 .. 20)

main :: Array String
main = do
  let positives = filter (_ > 0) (map (_ - 5) (1 .. 100))
  let unknownLengthRunsInVectors = sum (map (_ * 2) positives)
  let prices = map toNumber (1 .. length positives)
  let numberSumOverRangeFoldsBuiltArray = foldl (+) 0.0 (map (\price -> price * 1.19) prices)
  [ show shortLiteralStaysScalar
  , show shortRangeStaysScalar
  , show unknownLengthRunsInVectors
  , show numberSumOverRangeFoldsBuiltArray
  ]
