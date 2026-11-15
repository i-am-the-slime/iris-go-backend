module Main where

import Prelude

import Data.Array as Array
import Data.Foldable (class Foldable, foldMapDefaultL, sum)
import Effect (Effect)

data List a = Nil | Cons a (List a)

foldlList :: forall a b. (b -> a -> b) -> b -> List a -> b
foldlList f = go
  where
  go accumulator Nil = accumulator
  go accumulator (Cons x xs) = go (f accumulator x) xs

instance Foldable List where
  foldl = foldlList
  foldr f b = foldlList (flip f) b <<< reverse
    where
    reverse = foldlList (flip Cons) Nil
  foldMap = foldMapDefaultL

main :: Effect Int
main = pure (sum (Array.fromFoldable (Cons 1 (Cons 2 Nil))))
