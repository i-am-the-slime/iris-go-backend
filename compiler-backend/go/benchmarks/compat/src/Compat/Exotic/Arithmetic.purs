module Compat.Exotic.Arithmetic where

import Prelude

import Data.Int (toNumber, floor, round, pow, quot, rem, fromString, toStringAs, hexadecimal, fromNumber)
import Data.Int.Bits (shl, shr, zshr, (.&.), (.|.), xor, complement)
import Data.Number as Number
import Effect (Effect)
import Effect.Console (log)

main :: Effect Unit
main = do
  log (show (top + 1 :: Int) <> " " <> show (bottom - 1 :: Int) <> " " <> show (top * 2 :: Int))
  log (show ((-7) / 2) <> " " <> show ((-7) `mod` 2) <> " " <> show (7 / (-2)) <> " " <> show (7 `mod` (-2)) <> " " <> show (5 / 0) <> " " <> show (5 `mod` 0))
  log (show (quot (-7) 2) <> " " <> show (rem (-7) 2))
  log (show (shl 1 31) <> " " <> show (shr (-16) 2) <> " " <> show (zshr (-16) 28) <> " " <> show (0xF0 .&. 0x3C) <> " " <> show (0xF0 .|. 0x0F) <> " " <> show (xor 5 3) <> " " <> show (complement 0))
  log (show (pow 2 30) <> " " <> show (pow 3 21))
  log (show (toNumber top + 1.0) <> " " <> show (1.0 / 0.0) <> " " <> show (0.0 / 0.0) <> " " <> show (-0.0))
  log (show 0.1 <> " " <> show (0.1 + 0.2) <> " " <> show 1.0e21 <> " " <> show 1.0e-7 <> " " <> show 123456789.125 <> " " <> show 5.0e-324)
  log (show (floor (-2.5)) <> " " <> show (round 2.5) <> " " <> show (round (-2.5)) <> " " <> show (fromNumber 3.0e10))
  log (show (fromString "0x10") <> " " <> show (fromString "-42") <> " " <> show (toStringAs hexadecimal (-255)))
  log (show (Number.sqrt 2.0) <> " " <> show (Number.pow 2.0 0.5) <> " " <> show (Number.trunc (-3.7)) <> " " <> show (Number.fromString "1e3"))
  log (show (1.0e300 * 1.0e10) <> " " <> show (top `div` (-1) :: Int) <> " " <> show (bottom `div` (-1) :: Int))
  log (show (degree 360) <> " " <> show (Number.abs (-0.0)))
  where
  degree n = toNumber n * Number.pi / 180.0
