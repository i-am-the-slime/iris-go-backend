module Main where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Maybe (Maybe(..), maybe)
import Data.Tuple.Nested (type (/\), (/\))

data Heap a = Leaf | Node Int a (Heap a) (Heap a)

insert :: forall a. Ord a => a -> Heap a -> Heap a
insert value heap = merge (Node 1 value Leaf Leaf) heap

smallest :: forall a. Heap a -> Maybe a
smallest = case _ of
  Leaf -> Nothing
  Node _ value _ _ -> Just value

withoutSmallest :: forall a. Ord a => Heap a -> Heap a
withoutSmallest = case _ of
  Leaf -> Leaf
  Node _ _ left right -> merge left right

merge :: forall a. Ord a => Heap a -> Heap a -> Heap a
merge Leaf heap = heap
merge heap Leaf = heap
merge first@(Node _ x left right) second@(Node _ y _ _)
  | x <= y = node x left (merge right second)
  | otherwise = merge second first

node :: forall a. a -> Heap a -> Heap a -> Heap a
node value a b
  | rank a >= rank b = Node (rank b + 1) value a b
  | otherwise = Node (rank a + 1) value b a

rank :: forall a. Heap a -> Int
rank = case _ of
  Leaf -> 0
  Node r _ _ _ -> r

churn :: Heap (Int /\ Int) -> Int -> Heap (Int /\ Int)
churn heap step = case smallest heap of
  Just (priority /\ label) -> insert ((priority + 1000) /\ (label + step)) (withoutSmallest heap)
  Nothing -> heap

main :: Int
main = Array.range 1 1000 # foldl churn filled # smallest # maybe 0 \(priority /\ label) -> priority + label
  where
  filled = Array.range 1 100 <#> (\n -> n /\ n) # foldl (flip insert) Leaf
