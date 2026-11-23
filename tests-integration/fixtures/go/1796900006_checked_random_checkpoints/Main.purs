module Main where

import Prelude

import Data.Foldable (sum)
import Data.List (List(..), filter, length, take, (:))
import RedBlack (Tree(..), checksum, insert, size, valid)

following :: Int -> Int
following state = (state * 75 + 74) `mod` 65537

type Run = { trees :: List Tree, folded :: Int }

run :: Int -> Int -> Run
run seed steps = go Leaf Nil 0 seed steps
  where
  go tree kept folded state n
    | n <= 0 = { trees: tree : kept, folded }
    | otherwise = do
        let next = following state
        let grown = insert (next `mod` 512) (next `mod` 3 == 0) tree
        let keeping = next `mod` 7 == 0
        let probing = next `mod` 11 == 0
        go grown (if keeping then grown : kept else kept) (if probing then folded + sum (map checksum (take 3 kept)) else folded) next (n - 1)

summary :: Run -> Array Int
summary { trees, folded } =
  [ length trees
  , sum (map size trees)
  , sum (map checksum trees)
  , length (filter (not <<< valid) trees)
  , folded
  ]

main :: Array Int
main = [ 1, 2, 3, 42, 1234 ] >>= \seed -> summary (run seed 3000)
