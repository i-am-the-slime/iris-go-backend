module Main where

import Prelude

import Data.Exists (Exists, mkExists, runExists)

data Tree a = Leaf a | Pair (Exists (PairE a))

data PairE a x = PairE (Tree (x -> a)) (Tree x)

pair :: forall a x. Tree (x -> a) -> Tree x -> Tree a
pair function argument = Pair (mkExists (PairE function argument))

leaves :: forall a. Tree a -> Int
leaves = go 0
  where
  go :: forall b. Int -> Tree b -> Int
  go depth (Leaf _) = depth + 1
  go depth (Pair nested) = runExists (\(PairE function argument) -> go (depth + 1) function + go (depth + 1) argument) nested

main :: Array Int
main =
  [ leaves (Leaf 1)
  , leaves (pair (Leaf (_ + 1)) (Leaf 1))
  , leaves (pair (pair (Leaf (\x y -> x + y)) (Leaf 1)) (Leaf 2))
  ]
