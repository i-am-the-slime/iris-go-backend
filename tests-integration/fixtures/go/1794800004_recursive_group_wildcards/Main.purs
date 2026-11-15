module Main where

import Prelude

import Data.Foldable (sum)
import Data.Tuple (Tuple(..))

data Tree a = Leaf a | Node (Array (Tree a))

count :: Array _ -> Int
count trees = sum (map size trees)

size :: _ -> Int
size tree = case tree of
  Leaf (Tuple _ n) -> n
  Node trees -> count trees

main :: Int
main = count [ Leaf (Tuple "a" 1), Node [ Leaf (Tuple "b" 2) ] ]
