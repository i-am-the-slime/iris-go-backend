module Bench.Idiom.Random
  ( xorshift
  , pseudoRandomArray
  ) where

import Prelude

import Data.Array as Array
import Data.Int.Bits (shl, xor, zshr)

xorshift :: Int -> Int
xorshift seed = do
  let a = seed `xor` (seed `shl` 13)
  let b = a `xor` (a `zshr` 17)
  b `xor` (b `shl` 5)

pseudoRandomArray :: Int -> Array Int
pseudoRandomArray count = map xorshift (Array.range 1 count)
