module Main where

import Prelude

import Data.Int (pow)

opaque :: Int -> Int
opaque x = if x == 12345 then opaque x else x

-- | Each line pairs a product the compiler folds with the same product computed at run time.
-- | Both wrap like int32: 123456789 * 987654321 is 121932631112635269, beyond 2^53, whose low
-- | 32 bits are -67153019, where JavaScript's `x * y | 0` rounds to a double first and gives
-- | -67153024.
pair :: Int -> Int -> String
pair folded computed = show folded <> "/" <> show computed

main :: Array String
main =
  [ pair (123456789 * 987654321) (opaque 123456789 * 987654321)
  , pair (2147483647 * 2147483647) (opaque 2147483647 * opaque 2147483647)
  , pair (65536 * 65536) (opaque 65536 * 65536)
  , pair (-7 * 6) (opaque (-7) * 6)
  , pair (pow 3 40) (pow (opaque 3) 40)
  , pair (pow 2 31) (pow (opaque 2) 31)
  , pair (pow 2 (-1)) (pow (opaque 2) (-1))
  , pair (pow (-1) (-3)) (pow (opaque (-1)) (-3))
  ]
