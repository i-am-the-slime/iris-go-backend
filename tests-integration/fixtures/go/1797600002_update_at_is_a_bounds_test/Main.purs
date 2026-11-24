module Main where

import Prelude

import Data.Array (index, updateAt)
import Data.Lens (set)
import Data.Lens.Index (ix)
import Data.Maybe (Maybe(..), fromMaybe)

-- | `ix 0` tests the bounds once: the copy with the new element needs no second test.
renamedFirst :: Array String -> Array String
renamedFirst items = set (ix 0) "better sword" items

-- | Matched at once, `updateAt` is the test it makes: a copy with the element replaced
-- | (`slices.Clone`, then an assignment) where the index is within the array.
replaced :: Int -> Array Int -> Array Int
replaced at numbers = fromMaybe numbers (updateAt at 0 numbers)

-- | Kept as a Maybe, it is built where the test passes.
attempted :: Int -> Array Int -> Maybe (Array Int)
attempted at numbers = updateAt at 9 numbers

-- | A test that a branch has already made is not made again inside it.
twice :: Array Int -> Int
twice numbers = case index numbers 1 of
  Just second -> case index numbers 1 of
    Just again -> second + again
    Nothing -> 0
  Nothing -> -1

main :: Array String
main =
  [ show (renamedFirst [ "sword", "map" ])
  , show (renamedFirst [])
  , show (replaced 1 [ 1, 2, 3 ])
  , show (replaced 5 [ 1, 2, 3 ])
  , show (attempted 0 [ 1 ])
  , show (attempted (-1) [ 1 ])
  , show (twice [ 1, 2 ])
  , show (twice [])
  ]
