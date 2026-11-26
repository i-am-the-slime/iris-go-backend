module Main where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..), fromMaybe)

doubled :: Int -> Array Int -> Array Int
doubled position values
  | Just current <- Array.index values position =
      doubled (position + 1) (fromMaybe values (Array.updateAt position (current * 2) values))
  | otherwise = values

main :: Array String
main = do
  let shared = Array.range 1 5
  [ show (doubled 0 shared)
  , show (doubled 3 shared)
  , show shared
  ]
