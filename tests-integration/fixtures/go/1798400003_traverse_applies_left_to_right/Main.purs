module Main where

import Prelude

import Data.Traversable (traverse)

newtype Shape a = Shape { shape :: String, value :: a }

instance Functor Shape where
  map f (Shape s) = Shape s { value = f s.value }

instance Apply Shape where
  apply (Shape f) (Shape a) = Shape { shape: "(" <> f.shape <> " " <> a.shape <> ")", value: f.value a.value }

instance Applicative Shape where
  pure value = Shape { shape: "pure", value }

shapeOf :: Array Int -> String
shapeOf xs = case traverse (\x -> Shape { shape: show x, value: x }) xs of
  Shape s -> s.shape

main :: Array String
main = [ shapeOf [], shapeOf [ 1, 2 ], shapeOf [ 1, 2, 3, 4, 5 ] ]
