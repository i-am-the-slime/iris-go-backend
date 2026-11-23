module Main where

import Prelude

import Data.Array as Array
import Data.Foldable (intercalate)

intercalatedArrayJoinsOnce :: Array String -> String
intercalatedArrayJoinsOnce words = intercalate ", " words

arrayIntercalateJoinsOnce :: Array String -> String
arrayIntercalateJoinsOnce words = Array.intercalate "-" words

intercalatedArraysStayAFold :: Array (Array Int) -> Array Int
intercalatedArraysStayAFold rows = intercalate [ 0 ] rows

main :: Array String
main =
  [ intercalatedArrayJoinsOnce [ "a", "b", "c" ]
  , arrayIntercalateJoinsOnce [ "x" ]
  , show (intercalatedArraysStayAFold [ [ 1 ], [ 2, 3 ] ])
  ]
