module Main where

import Prelude

relate :: forall a. Ord a => Int -> a -> a -> String
relate 0 left right
  | left == right = "equal"
  | otherwise = show (compare left right)
relate depth left right = relate (depth - 1) [ left ] [ right, right ]

main :: Array String
main = [ relate 2 1 1, relate 2 'a' 'b' ]
