module Main where

import Prelude

import Data.Array (foldl, foldr, length, mapWithIndex, (..))
import Data.Foldable (for_)
import Effect.Ref as Ref
import Effect.Unsafe (unsafePerformEffect)

-- A range read once by a fold or a loop is counted through, never built: a
-- support function works out which way the range runs and how many elements
-- it has, and a mapped range allocates its result at that length.
summed :: Int -> Int -> Int
summed first last = foldl (+) 0 (first .. last)

listed :: Int -> String
listed n = foldr (\x rest -> show x <> "," <> rest) "" (n .. 1)

counted :: Int -> Int
counted n = length (1 .. n)

indexed :: Int -> Array Int
indexed n = mapWithIndex (\index x -> index * x) (1 .. n)

descending :: Array Int
descending = map (_ * 2) (3 .. 1)

-- The bounds come from a `Ref`, so that only the running program knows them.
-- The effects of a `for_` over a range run in the range's order.
main
  :: { visited :: Array Int
     , summed :: Int
     , listed :: String
     , counted :: Int
     , indexed :: Array Int
     , descending :: Array Int
     }
main = unsafePerformEffect do
  bound <- Ref.new 4
  n <- Ref.read bound
  seen <- Ref.new []
  for_ (n .. 1) \i -> Ref.modify_ (_ <> [ i ]) seen
  visited <- Ref.read seen
  pure { visited, summed: summed 1 n, listed: listed n, counted: counted n, indexed: indexed n, descending }
