module Main where

import Prelude

import Data.Foldable (foldl)
import Data.Tuple (Tuple(..))

-- `Sequence` is non-regular, so its element fields are erased for every
-- instantiation; patterns at `Sequence Int` convert the fields they bind.

data Sequence a = Empty | Zero (Sequence (Tuple a a)) | One a (Sequence (Tuple a a))

cons :: forall a. a -> Sequence a -> Sequence a
cons x = case _ of
  Empty -> One x Empty
  Zero rest -> One x rest
  One y rest -> Zero (cons (Tuple x y) rest)

classify :: Sequence Int -> Int
classify = case _ of
  One 1 _ -> 100
  One x (One (Tuple a b) _) -> x + a * 10 + b
  One x _ -> x
  Zero (One (Tuple a b) _) -> a - b
  _ -> 0

main :: Array Int
main = map (classify <<< foldl (flip cons) Empty) [ [ 1 ], [ 1, 2, 3 ], [ 4, 5, 6 ], [ 9, 3 ], [] ]
