module Main where

import Prelude

import Data.Array as Array
import Partial.Unsafe (unsafePartial)

allPositiveFrom :: Int -> Array Int -> Boolean
allPositiveFrom i xs = i >= Array.length xs || (unsafePartial (Array.unsafeIndex xs i) > 0 && allPositiveFrom (i + 1) xs)

anyNegativeFrom :: Int -> Array Int -> Boolean
anyNegativeFrom i xs = i < Array.length xs && (unsafePartial (Array.unsafeIndex xs i) < 0 || anyNegativeFrom (i + 1) xs)

ascending :: Array Int -> Boolean
ascending xs = go 1
  where
  go i = i >= Array.length xs || unsafePartial (Array.unsafeIndex xs (i - 1) <= Array.unsafeIndex xs i) && go (i + 1)

isEven :: Int -> Boolean
isEven n = n == 0 || n > 0 && isOdd (n - 1)

isOdd :: Int -> Boolean
isOdd n = n /= 0 && n > 0 && isEven (n - 1)

main :: Array Boolean
main =
  [ allPositiveFrom 0 (Array.range 1 1000000)
  , allPositiveFrom 0 [ 1, 2, -3 ]
  , anyNegativeFrom 0 (Array.range 1 1000000)
  , anyNegativeFrom 0 [ 1, 2, -3 ]
  , ascending (Array.range 1 1000000)
  , ascending [ 1, 3, 2 ]
  , isEven 1000000
  , isOdd 7
  ]
