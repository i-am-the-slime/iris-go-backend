module Main where

import Prelude

import Data.Array (filter, findLastIndex, foldr)
import Data.Maybe (Maybe)

-- `foldr` over a `map` walks the source backwards and maps each element on the
-- way; over a `filter` it keeps the filtered array, which it cannot index.
main :: { overMap :: String, overFilter :: String, lastSmall :: Maybe Int }
main =
  { overMap: foldr (\x rest -> show x <> "," <> rest) "" (map (_ * 2) numbers)
  , overFilter: foldr (\x rest -> show x <> ";" <> rest) "" (filter (_ > 2) numbers)
  , lastSmall: findLastIndex (_ < 5) (map (_ * 2) numbers)
  }

numbers :: Array Int
numbers = [ 3, 1, 4, 1, 5, 9, 2, 6 ]
