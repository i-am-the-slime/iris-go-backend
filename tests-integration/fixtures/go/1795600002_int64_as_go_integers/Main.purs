module Main where

import Prelude

import Data.Foldable (foldl)
import Data.Int64 (Int64)
import Data.Int64 as Int64
import Data.Maybe (Maybe)
import Data.UInt64 (UInt64)
import Data.UInt64 as UInt64

-- | An Int64 is a Go int64 and a UInt64 a uint64, so their arrays are []int64 and []uint64, and
-- | their sums fold as vector lanes.
total :: Array Int64 -> Int64
total xs = foldl (+) zero xs

totalUnsigned :: Array UInt64 -> UInt64
totalUnsigned xs = foldl (+) zero xs

largest :: Array Int64 -> Int64
largest xs = foldl max bottom xs

offsets :: Int64 -> Array Int64 -> Array Int64
offsets base xs = map (\x -> x - base) xs

-- | 64-bit vectors cannot multiply, so a product keeps its scalar loop of Go's wrapping `*`.
product :: Array Int64 -> Int64
product xs = foldl (*) one xs

-- | Arithmetic, bit operations and comparisons are Go's operators on the Longs' own types.
polynomial :: Int64 -> Int64
polynomial x = x * x + Int64.fromInt 3 * x - one

mixed :: Int64 -> Int64 -> Int64
mixed x n = Int64.shl x n `Int64.xor` Int64.zshr x n

wrapped :: UInt64 -> UInt64
wrapped x = UInt64.shr (x - one) (UInt64.unsafeFromInt 1)

ordered :: Int64 -> Int64 -> Boolean
ordered x y = x < y && Int64.even y

-- | Constants fold as the Longs wrap, without Go's checks for constants that overflow.
wrapsAtCompileTime :: Int64
wrapsAtCompileTime = top + one

-- | What Go has no operator for is a function of iris-go's runtime: generic in the Long, or
-- | one per signedness when only its result has it.
quotients :: Int64 -> Int64 -> Int64
quotients x y = x / y + Int64.quot x y

parsed :: String -> Maybe UInt64
parsed = UInt64.fromString

converted :: Int64 -> UInt64
converted = Int64.toUnsigned

main :: Array String
main = do
  let xs = map Int64.fromInt [ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33 ]
  let us = map UInt64.unsafeFromInt [ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33 ]
  [ show (total xs), show (totalUnsigned us), show (largest xs), show (offsets one xs), show (product xs)
  , show (map polynomial xs), show (map (\x -> mixed x x) xs), show (wrapped zero)
  , show (map (ordered one) xs), show wrapsAtCompileTime, show (map (quotients (Int64.fromInt (-7))) xs)
  , show (parsed "18446744073709551615"), show (converted (negate one))
  ]
