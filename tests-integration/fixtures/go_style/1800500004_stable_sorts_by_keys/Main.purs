module Main where

import Prelude

import Data.Array as Array
import Data.Array.ST as STArray
import Data.Ord (comparing)
import Data.Ord.Down (Down(..))
import Effect (Effect)
import Effect.Console (logShow)

type Interval = { start :: Int, end :: Int, name :: String }

data Colour = Red | Green | Blue

derive instance Eq Colour
derive instance Ord Colour

main :: Effect Unit
main = do
  logShow (Array.sortWith _.start intervals <#> _.end)
  logShow (Array.sortWith _.name intervals <#> _.end)
  logShow (Array.sortWith (Down <<< _.start) intervals <#> _.end)
  logShow (Array.sortBy (flip (comparing _.start)) intervals <#> _.end)
  logShow (Array.sortWith colour intervals <#> _.end)
  logShow (sortedInPlace <#> _.end)
  logShow (Array.sortWith _.start ([] :: Array Interval) <#> _.end)
  where
  intervals = Array.range 1 25 <#> \n -> { start: (n * 7) `mod` 5 - 2, end: n, name: show ((n * 3) `mod` 4) }
  colour { end } = case end `mod` 3 of
    0 -> Blue
    1 -> Red
    _ -> Green
  sortedInPlace = STArray.run do
    cells <- STArray.thaw intervals
    STArray.sortWith _.start cells
