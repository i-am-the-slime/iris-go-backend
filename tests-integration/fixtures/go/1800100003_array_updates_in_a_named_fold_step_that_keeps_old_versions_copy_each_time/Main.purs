module Main where

import Prelude

import Data.Array ((..))
import Data.Array as Array
import Data.Foldable (foldl)
import Data.Maybe (fromMaybe)
import Data.Tuple.Nested (type (/\), (/\))

remembered :: Array Int /\ Array (Array Int) -> Int -> Array Int /\ Array (Array Int)
remembered (current /\ history) position =
  fromMaybe current (Array.updateAt position 7 current) /\ Array.snoc history current

keptVersions :: Array Int -> Array Int /\ Array (Array Int)
keptVersions values = foldl remembered (values /\ []) (0 .. 2)

main :: Array String
main = do
  let shared = Array.replicate 4 0
  [ show (keptVersions shared)
  , show shared
  ]
