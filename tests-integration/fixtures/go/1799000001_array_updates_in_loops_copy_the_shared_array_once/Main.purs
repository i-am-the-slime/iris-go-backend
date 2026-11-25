module Main where

import Prelude

import Data.Array ((..))
import Data.Array as Array
import Data.Foldable (foldl)
import Data.Maybe (fromMaybe)
import Data.Tuple.Nested (type (/\), (/\))

bumped :: Array Int -> Array Int
bumped values = foldl bump values (0 .. 9)
  where
  bump current position = fromMaybe current (Array.modifyAt position (_ + 1) current)

overwritten :: Array Int -> Array Int
overwritten values = foldl overwrite values (0 .. 4)
  where
  overwrite current position = fromMaybe current (Array.updateAt position (position * 3) current)

countedUp :: Int -> Array Int -> Array Int
countedUp position values
  | position >= Array.length values = values
  | otherwise = countedUp (position + 1) (fromMaybe values (Array.updateAt position position values))

keptVersions :: Array Int -> Array Int /\ Array (Array Int)
keptVersions values = foldl step (values /\ []) (0 .. 2)
  where
  step (current /\ history) position =
    fromMaybe current (Array.updateAt position 7 current) /\ Array.snoc history current

main :: Array String
main = do
  let shared = Array.replicate 6 0
  [ show (bumped shared)
  , show (overwritten shared)
  , show (countedUp 0 shared)
  , show (keptVersions shared)
  , show shared
  ]
