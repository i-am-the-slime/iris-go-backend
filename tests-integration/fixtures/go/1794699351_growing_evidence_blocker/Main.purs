module Main where

import Prelude

import Data.Foldable (class Foldable, foldMap, foldl, foldr, length)
import Native as Native

data Wrapped f a = Wrapped (f a)

instance Foldable f => Foldable (Wrapped f) where
  foldr step initial (Wrapped inner) = foldr step initial inner
  foldl step initial (Wrapped inner) = foldl step initial inner
  foldMap visit (Wrapped inner) = foldMap visit inner

count :: forall f. Foldable f => Int -> f Int -> Int
count 0 values = length values
count n values = count (n - 1) (Wrapped values)

main :: Array String
main = [ show (count 3 [ 1, 2 ]), Native.describe 1 ]
