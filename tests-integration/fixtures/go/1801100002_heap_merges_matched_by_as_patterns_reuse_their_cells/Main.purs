module Main where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Maybe (Maybe(..))

data Heap = Leaf | Node Int Int Heap Heap

insert :: Int -> Heap -> Heap
insert value heap = merge (Node 1 value Leaf Leaf) heap

smallest :: Heap -> Maybe Int
smallest = case _ of
  Leaf -> Nothing
  Node _ value _ _ -> Just value

withoutSmallest :: Heap -> Heap
withoutSmallest = case _ of
  Leaf -> Leaf
  Node _ _ left right -> merge left right

merge :: Heap -> Heap -> Heap
merge Leaf heap = heap
merge heap Leaf = heap
merge first@(Node _ x left right) second@(Node _ y _ _)
  | x <= y = node x left (merge right second)
  | otherwise = merge second first

node :: Int -> Heap -> Heap -> Heap
node value a b
  | rank a >= rank b = Node (rank b + 1) value a b
  | otherwise = Node (rank a + 1) value b a

rank :: Heap -> Int
rank = case _ of
  Leaf -> 0
  Node r _ _ _ -> r

-- | Pops every arrival, and sends two later ones from each early one.
settle :: Heap -> Int -> Int
settle frontier total = case smallest frontier of
  Nothing -> total
  Just arrival
    | arrival > 500 -> settle (withoutSmallest frontier) (total + 1)
    | otherwise -> settle (foldl (sendFrom arrival) (withoutSmallest frontier) [ 3, 7 ]) (total + arrival)
  where
  sendFrom arrival heap delay = insert (arrival + delay) heap

main :: Int
main = Array.range 1 20 # foldl (\total start -> total + settle (insert start Leaf) 0) 0
