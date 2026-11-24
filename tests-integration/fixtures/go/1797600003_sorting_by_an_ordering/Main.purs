module Main where

import Prelude

import Control.Monad.ST as ST
import Data.Array (sortBy)
import Data.Array.ST as STArray
import Data.Ordering (invert)

data Suit = Hearts | Spades | Clubs

derive instance Eq Suit
derive instance Ord Suit

instance Show Suit where
  show Hearts = "hearts"
  show Spades = "spades"
  show Clubs = "clubs"

-- | A comparison the backend cannot read as keys sorts with a comparator that returns an int,
-- | as `slices.SortStableFunc` takes one: the Ordering becomes -1, 0 or 1 inside it.
bySuit :: Array Suit -> Array Suit
bySuit = sortBy compare

descending :: Array Suit -> Array Suit
descending = sortBy (\a b -> invert (compare a b))

-- | Sorting a mutable array in place takes the same comparator.
sortedInPlace :: Array Suit -> Array Suit
sortedInPlace suits = ST.run do
  array <- STArray.thaw suits
  _ <- STArray.sortBy compare array
  STArray.unsafeFreeze array

main :: Array String
main =
  [ show (bySuit [ Clubs, Hearts, Spades, Hearts ])
  , show (descending [ Clubs, Hearts, Spades ])
  , show (sortedInPlace [ Spades, Clubs, Hearts ])
  ]
