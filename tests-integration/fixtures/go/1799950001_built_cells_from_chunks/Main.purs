module Main where

import Prelude

data Tree = Leaf | Node Tree Int Tree

fullTreeIsBuiltFromOneChunk :: Int -> Tree
fullTreeIsBuiltFromOneChunk depth
  | depth == 0 = Leaf
  | otherwise = Node (fullTreeIsBuiltFromOneChunk (depth - 1)) depth (fullTreeIsBuiltFromOneChunk (depth - 1))

inspectedResultIsNotChunked :: Int -> Tree
inspectedResultIsNotChunked depth
  | depth == 0 = Leaf
  | otherwise = case inspectedResultIsNotChunked (depth - 1) of
      Node left _ _ -> Node left depth Leaf
      Leaf -> Node Leaf depth Leaf

insertCopiesItsPathCellByCell :: Int -> Tree -> Tree
insertCopiesItsPathCellByCell value = case _ of
  Leaf -> Node Leaf value Leaf
  Node left key right
    | value < key -> Node (insertCopiesItsPathCellByCell value left) key right
    | otherwise -> Node left key (insertCopiesItsPathCellByCell value right)

total :: Tree -> Int
total = case _ of
  Leaf -> 0
  Node left value right -> total left + value + total right

main :: Array Int
main = do
  let full = fullTreeIsBuiltFromOneChunk 4
  [ total full
  , total (inspectedResultIsNotChunked 4)
  , total (insertCopiesItsPathCellByCell 5 full)
  , total full
  ]
