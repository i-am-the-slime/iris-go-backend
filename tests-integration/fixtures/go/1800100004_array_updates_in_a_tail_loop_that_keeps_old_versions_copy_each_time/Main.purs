module Main where

import Prelude

import Data.Array as Array
import Data.Maybe (fromMaybe)

versions :: Int -> Array Int -> Array (Array Int) -> Array (Array Int)
versions position values history
  | position >= Array.length values = Array.snoc history values
  | otherwise =
      versions (position + 1) (fromMaybe values (Array.updateAt position 1 values)) (Array.snoc history values)

main :: Array String
main = do
  let shared = Array.replicate 3 0
  [ show (versions 0 shared [])
  , show shared
  ]
