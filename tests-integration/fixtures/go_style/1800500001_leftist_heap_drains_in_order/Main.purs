module Main where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested (type (/\), (/\))
import Data.Unfoldable (unfoldr)
import Effect (Effect)
import Effect.Console (logShow)

data Heap a = Leaf | Node Int a (Heap a) (Heap a)

main :: Effect Unit
main = do
  logShow (drained (Array.range 1 40 <#> scrambled # foldl (flip insert) Leaf))
  logShow (Array.range 1 2000 # foldl churn (Array.range 1 50 <#> scrambled # foldl (flip insert) Leaf) # smallest)
  where
  scrambled n = (n * 37) `mod` 101 /\ n
  churn heap step = case smallest heap of
    Just (priority /\ label) -> insert ((priority + step) /\ label) (withoutSmallest heap)
    Nothing -> heap

drained :: forall a. Ord a => Heap a -> Array a
drained = unfoldr \heap -> smallest heap <#> \value -> value /\ withoutSmallest heap

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
