module Main where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Journal (log)

main :: Effect Unit
main = do
  log (show (sumUncons (Array.range 1 1000)))
  log (show (lastOfUnsnoc [ 3, 1, 4, 1, 5 ]))

sumUncons :: Array Int -> Int
sumUncons xs = go 0 xs
  where
  go total rest = case Array.uncons rest of
    Nothing -> total
    Just { head, tail } -> go (total + head) tail

lastOfUnsnoc :: Array Int -> Int
lastOfUnsnoc xs = go 0 xs
  where
  go weighted rest = case Array.unsnoc rest of
    Nothing -> weighted
    Just { init, last } -> go (weighted * 10 + last) init
