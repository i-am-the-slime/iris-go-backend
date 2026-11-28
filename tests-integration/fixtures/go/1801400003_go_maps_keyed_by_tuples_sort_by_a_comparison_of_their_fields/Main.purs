module Main where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Map (Map)
import Data.Map as Map
import Data.Tuple.Nested (type (/\), (/\))

grid :: Int -> Map (Int /\ String) Int
grid n = foldl (\m k -> Map.insert (k `mod` 7 /\ show (k `mod` 3)) k m) Map.empty (Array.range 1 n)

labelled :: Int -> Map { row :: Int, column :: Int } Int
labelled n = foldl (\m k -> Map.insertWith (+) { row: k `mod` 4, column: k `mod` 5 } k m) Map.empty (Array.range 1 n)

main :: Int
main = foldl (+) 0 (grid 40) + foldl (\total value -> total * 3 + value) 0 (labelled 40)
