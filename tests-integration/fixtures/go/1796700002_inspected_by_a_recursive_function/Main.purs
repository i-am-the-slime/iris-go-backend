module Main where

import Prelude

data Tree = Leaf | Node Tree Int Tree

insert :: Int -> Tree -> Tree
insert key = case _ of
  Leaf -> Node Leaf key Leaf
  Node left value right
    | key < value -> Node (insert key left) value right
    | key > value -> Node left value (insert key right)
    | otherwise -> Node left value right

size :: Tree -> Int
size = case _ of
  Leaf -> 0
  Node left _ right -> size left + 1 + size right

deepest :: Int -> Tree -> Int
deepest depth = case _ of
  Leaf -> depth
  Node left _ right -> max (deepest (depth + 1) left) (deepest (depth + 1) right)

grown :: Int -> Tree -> Tree
grown limit tree
  | size tree >= limit = tree
  | otherwise = grown limit (insert ((size tree * 7) `mod` 13) tree)

elements :: Tree -> String
elements = case _ of
  Leaf -> ""
  Node left value right -> elements left <> " " <> show value <> elements right

main :: String
main = do
  let tree = grown 10 Leaf
  show (deepest 0 tree) <> ":" <> elements (insert 6 tree)
