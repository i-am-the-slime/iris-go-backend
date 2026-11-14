module Main where

import Prelude

import Data.Array as Array
import Data.Lazy as Lazy

chain :: Int -> (Int -> Int) -> Int -> Int
chain 0 k = k
chain n k = chain (n - 1) \x -> k (x + 1)

thunks :: Int -> (Unit -> Int) -> Unit -> Int
thunks 0 t = t
thunks n t = thunks (n - 1) \_ -> t unit + 1

main :: { summed :: Int, memoised :: Int }
main =
  { summed: Array.foldl (\total k -> total + k 1) 0 [ chain 2 identity, chain 3 identity ]
  , memoised: Lazy.force (Lazy.defer (thunks 3 \_ -> 0))
  }
