module Main where

import Prelude

import Data.Foldable (sum)
import Data.List (List(..), filter, length, (:))
import RedBlack (Tree(..), checksum, insert, size, valid)

checkpoints :: Int -> Int -> List Tree
checkpoints frequency = go Leaf Nil
  where
  go tree kept n
    | n <= 0 = tree : kept
    | otherwise = do
        let next = insert n (n `mod` 10 == 0) tree
        go next (if n `mod` frequency == 0 then next : kept else kept) (n - 1)

main :: Array Int
main = do
  let trees = checkpoints 5 2000
  [ length trees
  , sum (map size trees)
  , sum (map checksum trees)
  , length (filter (not <<< valid) trees)
  ]
