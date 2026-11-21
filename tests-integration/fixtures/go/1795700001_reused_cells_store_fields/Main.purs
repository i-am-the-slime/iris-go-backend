module Main where

import Prelude

data Tree = Leaf | Node Int Int Tree Tree

data Chain = End | Red Int Chain | Blue Int Chain

insertCounts :: Int -> Tree -> Tree
insertCounts key = case _ of
  Leaf -> Node key 1 Leaf Leaf
  Node k count left right
    | key < k -> Node k count (insertCounts key left) right
    | key > k -> Node k count left (insertCounts key right)
    | otherwise -> Node k (count + 1) left right

recolourStoresTheTag :: Chain -> Chain
recolourStoresTheTag = case _ of
  Red n rest -> Blue (n + 1) (recolourStoresTheTag rest)
  Blue n rest -> Red n (recolourStoresTheTag rest)
  End -> End

blues :: Chain -> Int
blues = case _ of
  Blue n rest -> n + blues rest
  Red _ rest -> blues rest
  End -> 0

sizeOf :: Tree -> Int
sizeOf Leaf = 0
sizeOf (Node _ count left right) = count + sizeOf left + sizeOf right

swapFieldsComputedFromTheCell :: Tree -> Tree
swapFieldsComputedFromTheCell = case _ of
  Node k count left right -> Node (count + sizeOf left) k right left
  Leaf -> Leaf

counts :: Tree
counts = insertCounts 2 (insertCounts 1 (insertCounts 2 Leaf))

main :: { size :: Int, swapped :: Int, blues :: Int }
main =
  { size: sizeOf counts
  , swapped: sizeOf (swapFieldsComputedFromTheCell (insertCounts 3 Leaf))
  , blues: blues (recolourStoresTheTag (Red 1 (Blue 2 (Red 3 End))))
  }
