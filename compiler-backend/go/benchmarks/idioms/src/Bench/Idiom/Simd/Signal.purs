module Bench.Idiom.Simd.Signal
  ( left
  , right
  , counts
  ) where

import Prelude

import Bench.Idiom.Random (xorshift)
import Data.Array as Array
import Data.Int (toNumber)

-- | Ten million samples in [-1, 1], like an audio buffer. The inputs are built once per program,
-- | so that each benchmark times its kernel rather than the noise generator.
left :: Array Number
left = samples 1

right :: Array Number
right = samples 7

-- | Ten million Ints in [0, 1000).
counts :: Array Int
counts = map (\i -> xorshift (i + 3) `mod` 1000) (Array.range 1 size)

samples :: Int -> Array Number
samples seed = map (\i -> toNumber (xorshift (i + seed) `mod` 2001 - 1000) * 0.001) (Array.range 1 size)

size :: Int
size = 10000000
