module Main where

import Prelude

import Data.Int64 (Int64)
import Data.Int64 as Int64
import Data.UInt64 (UInt64)
import Data.UInt64 as UInt64

-- | A divisor that is a constant other than zero needs no zero test, and Go's `/` and `%`
-- | truncate as long.js's `div` and `mod` do: -7 `quot` 2 is -3 and -7 `rem` 2 is -1.
halved :: Int64 -> Int64
halved x = Int64.quot x (Int64.fromInt 2) * Int64.fromInt 10 + Int64.rem x (Int64.fromInt 2)

-- | Euclidean `div` and `mod` by a constant: -7 / 2 is -4 and -7 `mod` 2 is 1.
euclidean :: Int64 -> Int64
euclidean x = x / Int64.fromInt 2 * Int64.fromInt 10 + x `mod` Int64.fromInt 2

-- | The most negative Long divided by -1 wraps to itself in long.js and in Go.
wrapping :: Int64 -> Int64
wrapping x = Int64.quot x (negate one)

unsignedHalf :: UInt64 -> UInt64
unsignedHalf x = x / (one + one)

-- | A divisor only known at run time keeps the runtime's zero test.
divided :: Int64 -> Int64 -> Int64
divided x y = Int64.quot x y

-- | Constant operands fold, the zero test of a constant divisor with them.
folded :: UInt64
folded = Int64.toUnsigned (negate one) / (one + one)

main :: Array String
main =
  [ show (map halved [ Int64.fromInt (-7), Int64.fromInt 7 ])
  , show (map euclidean [ Int64.fromInt (-7), Int64.fromInt 7 ])
  , show (wrapping bottom)
  , show (unsignedHalf (UInt64.unsafeFromInt 9))
  , show (divided (Int64.fromInt 9) (Int64.fromInt 0))
  , show folded
  ]
