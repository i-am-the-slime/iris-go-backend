module Main where

import Prelude

import Data.Foldable (foldl)

data Pair a = Pair a a

data Sequence a = Empty | Zero (Sequence (Pair a)) | One a (Sequence (Pair a))

value :: Pair Int -> Int
value (Pair first second) = if first > 100 then value (Pair (first - 100) second) else first * 10 + second

cons :: forall a. a -> Sequence a -> Sequence a
cons x = case _ of
  Empty -> One x Empty
  Zero rest -> One x rest
  One y rest -> Zero (cons (Pair x y) rest)

classify :: Sequence Int -> Int
classify = case _ of
  One x (One pair _) -> x + value pair
  Zero (One pair _) -> value pair
  One x _ -> x
  _ -> 0

main :: Array Int
main = map (classify <<< foldl (flip cons) Empty) [ [ 1 ], [ 1, 2, 3 ], [ 4, 5, 6 ], [ 9, 3 ], [] ]
