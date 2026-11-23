module Main where

import Prelude

import Data.Foldable (sum)
import Data.List (List(..), filter, length, (:))
import RedBlack (Tree(..), checksum, insert, size, valid)

base :: Int -> Tree
base count = go Leaf count
  where
  go tree n
    | n <= 0 = tree
    | otherwise = go (insert (n * 16) false tree) (n - 1)

alternating :: Int -> List Tree
alternating steps = go (base 64) Nil steps
  where
  go tree kept n
    | n <= 0 = tree : kept
    | otherwise = do
        let key = if n `mod` 2 == 0 then n else 100000 - n
        let next = insert key (n `mod` 3 == 0) tree
        go next (if n `mod` 8 == 0 then next : kept else kept) (n - 1)

main :: Array Int
main = do
  let trees = alternating 1000
  [ length trees
  , sum (map size trees)
  , sum (map checksum trees)
  , length (filter (not <<< valid) trees)
  ]
