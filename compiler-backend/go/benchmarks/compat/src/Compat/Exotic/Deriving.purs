module Compat.Exotic.Deriving where

import Prelude

import Data.Foldable (class Foldable, foldr, sum, length)
import Data.Traversable (class Traversable, traverse, sequence)
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested ((/\))
import Data.Map as Map
import Data.Set as Set
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Effect (Effect)
import Effect.Console (log)

data Tree a = Leaf | Node (Tree a) a (Tree a)

derive instance Eq a => Eq (Tree a)
derive instance Ord a => Ord (Tree a)
derive instance Functor Tree
derive instance Foldable Tree
derive instance Traversable Tree
derive instance Generic (Tree a) _
instance Show a => Show (Tree a) where
  show t = genericShow t

data Rose f a = Rose a (f (Rose f a))

derive instance Functor f => Functor (Rose f)
derive instance Foldable f => Foldable (Rose f)

data Shape = Circle { radius :: Number } | Polygon (Array { x :: Int, y :: Int }) | Empty

derive instance Eq Shape
derive instance Ord Shape

newtype Wrapper a = Wrapper { value :: a, label :: String }

derive instance Functor Wrapper
derive instance Eq a => Eq (Wrapper a)

data Priority = Low | Medium | High

derive instance Eq Priority
derive instance Ord Priority
derive instance Generic Priority _
instance Show Priority where
  show = genericShow

insert :: forall a. Ord a => a -> Tree a -> Tree a
insert x Leaf = Node Leaf x Leaf
insert x t@(Node l v r) = case compare x v of
  LT -> Node (insert x l) v r
  GT -> Node l v (insert x r)
  EQ -> t

main :: Effect Unit
main = do
  let tree = foldr insert Leaf [ 5, 2, 8, 1, 9 ]
  log (show tree)
  log (show (map (_ * 2) tree))
  log (show (sum tree) <> " " <> show (length tree :: Int))
  log (show (traverse (\x -> if x > 0 then Just x else Nothing) tree))
  log (show (sequence (Node Leaf [ 1, 2 ] Leaf)))
  log (show (compare tree (map (_ + 0) tree)) <> " " <> show (tree < Node Leaf 0 Leaf))
  let rose = Rose 1 [ Rose 2 [], Rose 3 [ Rose 4 [] ] ]
  log (show (sum rose) <> " " <> show (sum (map (_ * 10) rose)))
  log (show (Circle { radius: 1.0 } < Polygon []) <> " " <> show (Polygon [ { x: 1, y: 2 } ] == Polygon [ { x: 1, y: 2 } ]) <> " " <> show (compare Empty (Circle { radius: 0.0 })))
  log (show (map (_ + 1) (Wrapper { value: 1, label: "l" }) == Wrapper { value: 2, label: "l" }))
  log (show (Set.toUnfoldable (Set.fromFoldable [ High, Low, Medium, Low ]) :: Array Priority))
  log (show (Map.toUnfoldable (Map.fromFoldable [ { k: High } /\ "h", { k: Low } /\ "l" ]) :: Array _))
