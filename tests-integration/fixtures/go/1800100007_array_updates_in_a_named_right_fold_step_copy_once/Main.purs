module Main where

import Prelude

import Data.Array ((..))
import Data.Array as Array
import Data.Foldable (foldr)
import Data.Maybe (fromMaybe)

squaredInto :: Int -> Array Int -> Array Int
squaredInto position current = fromMaybe current (Array.updateAt position (position * position) current)

squares :: Array Int -> Array Int
squares values = foldr squaredInto values (0 .. 3)

main :: Array String
main = do
  let shared = Array.replicate 5 1
  [ show (squares shared)
  , show (squares [])
  , show shared
  ]
