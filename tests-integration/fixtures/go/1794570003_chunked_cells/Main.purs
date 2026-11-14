module Main where

import Prelude

data List a = Nil | Cons a (List a)

data Tree = Leaf | Node Tree Int Tree

rangeLinksEachCellToTheLast :: Int -> Int -> List Int
rangeLinksEachCellToTheLast start end = go end Nil
  where
  go current accumulator =
    if current < start then accumulator
    else go (current - 1) (Cons current accumulator)

spineLinksNestedCells :: Int -> Tree
spineLinksNestedCells depth = go depth Leaf
  where
  go remaining tree =
    if remaining <= 0 then tree
    else go (remaining - 1) (Node tree remaining (Node Leaf (remaining * 2) Leaf))

largestReplacesItsCell :: List Int -> List Int
largestReplacesItsCell = go Nil
  where
  go best Nil = best
  go best (Cons value rest) = case best of
    Cons known _ | known >= value -> go best rest
    _ -> go (Cons value Nil) rest

total :: Tree -> Int
total Leaf = 0
total (Node left value right) = total left + value + total right

main :: { numbers :: List Int, largest :: List Int, ownedLargest :: List Int, total :: Int }
main =
  { numbers
  , largest: largestReplacesItsCell numbers
  , ownedLargest: largestReplacesItsCell (rangeLinksEachCellToTheLast 1 10)
  , total: total (spineLinksNestedCells 5)
  }
  where
  numbers = rangeLinksEachCellToTheLast 1 20
