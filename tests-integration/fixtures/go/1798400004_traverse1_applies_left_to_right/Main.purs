module Main where

import Prelude

import Data.Array.NonEmpty (NonEmptyArray)
import Data.Array.NonEmpty as NonEmptyArray
import Data.Semigroup.Traversable (traverse1)

newtype Shape a = Shape { shape :: String, value :: a }

instance Functor Shape where
  map f (Shape s) = Shape s { value = f s.value }

instance Apply Shape where
  apply (Shape f) (Shape a) = Shape { shape: "(" <> f.shape <> " " <> a.shape <> ")", value: f.value a.value }

shapeOf :: NonEmptyArray Int -> String
shapeOf xs = case traverse1 (\x -> Shape { shape: show x, value: x }) xs of
  Shape s -> s.shape

valuesOf :: NonEmptyArray Int -> String
valuesOf xs = case traverse1 (\x -> Shape { shape: "", value: x * 10 }) xs of
  Shape s -> show s.value

main :: Array String
main =
  [ shapeOf (NonEmptyArray.singleton 1)
  , shapeOf (NonEmptyArray.cons' 1 [ 2 ])
  , shapeOf (NonEmptyArray.cons' 1 [ 2, 3, 4, 5 ])
  , valuesOf (NonEmptyArray.cons' 1 [ 2, 3 ])
  ]
