module Main where

import Prelude

import Data.Array (snoc)
import Data.Tuple.Nested ((/\), type (/\))

data Tree = Leaf | Node Tree Int Tree

inserted :: Int -> Tree -> Tree
inserted key = case _ of
  Leaf -> Node Leaf key Leaf
  Node left here right
    | key < here -> Node (inserted key left) here right
    | key > here -> Node left here (inserted key right)
    | otherwise -> Node left key right

total :: Tree -> Int
total = case _ of
  Leaf -> 0
  Node left here right -> total left + here + total right

-- | Every third tree is kept, so later insertions must copy the paths they change instead of
-- | overwriting the kept trees.
checkpointed :: Int -> Tree /\ Array Tree
checkpointed count = go Leaf [] count
  where
  go tree checkpoints remaining
    | remaining <= 0 = tree /\ checkpoints
    | otherwise = do
        let next = inserted remaining tree
        go next (keptEveryThird remaining next checkpoints) (remaining - 1)
  keptEveryThird remaining tree checkpoints
    | remaining `mod` 3 == 0 = snoc checkpoints tree
    | otherwise = checkpoints

-- | Nothing keeps these trees, so each insertion overwrites the cells it rebuilds.
unshared :: Int -> Tree
unshared count = go Leaf count
  where
  go tree remaining
    | remaining <= 0 = tree
    | otherwise = go (inserted remaining tree) (remaining - 1)

main :: Array Int
main = do
  let latest /\ checkpoints = checkpointed 9
  [ total latest, total (unshared 9) ] <> (checkpoints <#> total)
