module Main where

import Prelude

import Data.Array as Array
import Data.Maybe (fromMaybe)

countedUp :: Int -> Array Int -> Array Int
countedUp position values
  | position >= Array.length values = values
  | otherwise = countedUp (position + 1) (fromMaybe values (Array.updateAt position position values))

main :: Array String
main = do
  let shared = Array.replicate 6 0
  [ show (countedUp 0 shared)
  , show (countedUp 3 shared)
  , show shared
  ]
