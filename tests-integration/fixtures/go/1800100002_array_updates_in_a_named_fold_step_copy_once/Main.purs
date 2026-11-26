module Main where

import Prelude

import Data.Array ((..))
import Data.Array as Array
import Data.Foldable (foldl)
import Data.Maybe (fromMaybe)

overwrite :: Array Int -> Int -> Array Int
overwrite current position = fromMaybe current (Array.updateAt position (position * 3) current)

overwritten :: Array Int -> Array Int
overwritten values = foldl overwrite values (0 .. 4)

main :: Array String
main = do
  let shared = Array.replicate 6 0
  [ show (overwritten shared)
  , show (overwrite shared 1)
  , show shared
  ]
