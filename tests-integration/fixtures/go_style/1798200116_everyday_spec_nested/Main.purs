module Spec.Nested where

import Prelude

import Data.Foldable (class Foldable, foldMap, foldl, foldr, sum)
import Data.Traversable (class Traversable, traverse, sequence)
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Console (log)

data Nested a = Flat a | Nest (Nested (Array a))

instance Show a => Show (Nested a) where
  show (Flat a) = "Flat " <> show a
  show (Nest inner) = "Nest (" <> show inner <> ")"

derive instance Eq a => Eq (Nested a)
derive instance Ord a => Ord (Nested a)

instance Functor Nested where
  map f (Flat a) = Flat (f a)
  map f (Nest inner) = Nest (inner <#> map f)

instance Foldable Nested where
  foldr f z (Flat a) = f a z
  foldr f z (Nest inner) = foldr (\as acc -> foldr f acc as) z inner
  foldl f z (Flat a) = f z a
  foldl f z (Nest inner) = foldl (\acc as -> foldl f acc as) z inner
  foldMap f (Flat a) = f a
  foldMap f (Nest inner) = foldMap (foldMap f) inner

instance Traversable Nested where
  traverse f (Flat a) = Flat <$> f a
  traverse f (Nest inner) = Nest <$> traverse (traverse f) inner
  sequence = traverse identity

depth :: forall a. Nested a -> Int
depth (Flat _) = 0
depth (Nest inner) = 1 + depth inner

deep :: Nested Int
deep = Nest (Nest (Flat [ [ 1, 2 ], [ 3 ] ]))

main :: Effect Unit
main = do
  log (show deep)
  log (show (deep == deep) <> " " <> show (deep == Nest (Flat [ 1 ])))
  log (show (compare deep (Nest (Flat [ 1 ]))))
  log (show (deep <#> (_ * 10)))
  log (show (sum deep) <> " " <> foldMap show deep <> " " <> show (foldr (\n acc -> [ n ] <> acc) [] deep) <> " " <> show (foldl (-) 100 deep))
  log (show (traverse (\n -> if n > 0 then Just (n + 1) else Nothing) deep))
  log (show (depth deep))
