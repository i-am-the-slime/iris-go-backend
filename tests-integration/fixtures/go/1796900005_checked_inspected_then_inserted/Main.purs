module Main where

import Prelude

import Data.Foldable (sum)
import Data.List (List(..), filter, length, (:))
import RedBlack (Tree(..), checksum, insert, size, valid)

member :: Int -> Tree -> Boolean
member key = case _ of
  Leaf -> false
  Node _ l k _ r
    | key < k -> member key l
    | key > k -> member key r
    | otherwise -> true

insertIfAbsent :: Int -> Tree -> Tree
insertIfAbsent key tree
  | member key tree = tree
  | otherwise = insert key true tree

inspectedThenInserted :: Int -> { inspected :: Int, trees :: List Tree }
inspectedThenInserted steps = go Leaf Nil 0 steps
  where
  go tree kept inspected n
    | n <= 0 = { inspected, trees: tree : kept }
    | otherwise = do
        let next = insertIfAbsent ((n * 37) `mod` 500) tree
        go next (if n `mod` 9 == 0 then next : kept else kept) (inspected + (if n `mod` 3 == 0 then checksum next else 0)) (n - 1)

main :: Array Int
main = do
  let result = inspectedThenInserted 1500
  [ result.inspected
  , length result.trees
  , sum (map size result.trees)
  , sum (map checksum result.trees)
  , length (filter (not <<< valid) result.trees)
  ]
