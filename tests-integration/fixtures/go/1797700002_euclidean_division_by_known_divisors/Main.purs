module Main where

import Prelude

-- | The Euclidean and the truncated remainder of -7 by 3 differ (2 and -1) but are zero
-- | together, so a remainder compared with zero is Go's `%`, also for a negative divisor.
divisibleByThree :: Int -> Boolean
divisibleByThree n = n `mod` 3 == 0

notDivisibleByMinusThree :: Int -> Boolean
notDivisibleByMinusThree n = n `mod` (-3) /= 0

-- | By a power of two a shift and a mask, which round towards negative infinity as `div` and
-- | `mod` do: -7 / 2 is -4 and -7 `mod` 4 is 1.
halvesAndQuarters :: Int -> Int
halvesAndQuarters n = n / 2 * 10 + n `mod` 4

-- | By another positive constant the runtime's helpers for a positive divisor: -7 / 3 is -3 and
-- | -7 `mod` 3 is 2.
thirds :: Int -> Int
thirds n = n / 3 * 10 + n `mod` 3

-- | A non-negative dividend gives truncated and Euclidean division the same result once the
-- | divisor is known not to be zero, whatever its sign: 10 / -3 is -3 and 10 `mod` -3 is 1.
tenOver :: Int -> Int
tenOver 0 = 0
tenOver d = 10 / d * 10 + 10 `mod` d

-- | A negative dividend keeps Euclidean division: -10 / 3 is -4, where Go's `/` gives -3.
minusTenOver :: Int -> Int
minusTenOver d = if d == 0 then 0 else (-10) / d

main :: Array String
main =
  [ show (map divisibleByThree [ -7, -6, 6, 7 ])
  , show (map notDivisibleByMinusThree [ -7, -6, 6, 7 ])
  , show (map halvesAndQuarters [ -7, -1, 7 ])
  , show (map thirds [ -7, -1, 7 ])
  , show (map tenOver [ -3, 0, 3, 4 ])
  , show (map minusTenOver [ -3, 0, 3 ])
  ]
