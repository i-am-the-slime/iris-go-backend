module Main where

import Prelude

import Data.Foldable (class Foldable, foldMap, foldl, foldr, sum)
import Data.Maybe (Maybe(..))
import Data.Traversable (class Traversable, traverse)

data Nested a = Flat a | Nest (Nested (Array a))

instance Show a => Show (Nested a) where
  show (Flat value) = "Flat " <> show value
  show (Nest inner) = "Nest (" <> show inner <> ")"

derive instance Eq a => Eq (Nested a)
derive instance Ord a => Ord (Nested a)

instance Functor Nested where
  map change (Flat value) = Flat (change value)
  map change (Nest inner) = Nest (inner <#> map change)

instance Foldable Nested where
  foldr step initial (Flat value) = step value initial
  foldr step initial (Nest inner) = foldr (\values rest -> foldr step rest values) initial inner
  foldl step initial (Flat value) = step initial value
  foldl step initial (Nest inner) = foldl (\rest values -> foldl step rest values) initial inner
  foldMap visit (Flat value) = visit value
  foldMap visit (Nest inner) = foldMap (foldMap visit) inner

instance Traversable Nested where
  traverse visit (Flat value) = Flat <$> visit value
  traverse visit (Nest inner) = Nest <$> traverse (traverse visit) inner
  sequence = traverse identity

positive :: Int -> Maybe Int
positive n = if n > 0 then Just (n + 1) else Nothing

deep :: Nested Int
deep = Nest (Nest (Flat [ [ 1, 2 ], [ 3 ] ]))

main :: Array String
main =
  [ show deep
  , show (deep == deep) <> " " <> show (deep == Nest (Flat [ 1 ]))
  , show (compare deep (Nest (Flat [ 1 ])))
  , show (deep <#> (_ * 10))
  , show (sum deep) <> " " <> foldMap show deep <> " " <> show (foldl (-) 100 deep)
  , show (traverse positive deep)
  ]
