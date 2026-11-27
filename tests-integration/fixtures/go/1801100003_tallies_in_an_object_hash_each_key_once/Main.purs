module Main where

import Prelude

import Data.Array as Array
import Data.Maybe (fromMaybe)
import Data.Tuple.Nested ((/\))
import Foreign.Object as Object

main :: Int
main = Object.size tallies + fromMaybe 0 (Object.lookup "7" tallies)
  where
  tallies = Object.fromFoldableWith (+) (Array.range 1 3000 <#> \n -> show (n `mod` 97) /\ 1)
