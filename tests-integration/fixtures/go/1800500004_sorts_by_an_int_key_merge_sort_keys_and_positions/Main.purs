module Main where

import Prelude

import Data.Array as Array
import Data.Array.ST as STArray
import Data.Ord (comparing)

type Interval = { start :: Int, end :: Int, name :: String }

intervals :: Array Interval
intervals = Array.range 1 12 <#> \n -> { start: (n * 7) `mod` 5, end: n, name: show ((n * 3) `mod` 4) }

main :: Array String
main =
  [ show (byStart <#> _.end)
  , show (byName <#> _.end)
  , show (byStartDescending <#> _.end)
  , show (sortedInPlace <#> _.end)
  ]
  where
  byStart = Array.sortWith _.start intervals
  byName = Array.sortWith _.name intervals
  byStartDescending = Array.sortBy (flip (comparing _.start)) intervals
  sortedInPlace = STArray.run do
    cells <- STArray.thaw intervals
    STArray.sortWith _.start cells
