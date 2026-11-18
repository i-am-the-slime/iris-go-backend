module Main where

import Prelude

import Data.Array as Array
import Data.List (List(..), (:))
import Data.Maybe (Maybe(..))
import Data.Set as Set

numbers :: List Int
numbers = 1 : 2 : 3 : Nil

words :: Set.Set String
words = Set.fromFoldable [ "b", "a" ]

main :: Int
main =
  Array.length (Array.fromFoldable numbers)
    + Array.length (Array.fromFoldable (Just "x"))
    + Array.length (Array.fromFoldable words)
