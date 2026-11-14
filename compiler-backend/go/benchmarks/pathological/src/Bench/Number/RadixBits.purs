module Bench.Number.RadixBits where

import Prelude

import Bench.Harness (benchmark)
import Data.Array ((..))
import Data.Foldable (foldl)
import Data.Int (fromStringAs, hexadecimal, radix, toStringAs, binary)
import Data.Int.Bits (complement, shl, shr, xor, zshr, (.&.), (.|.))
import Data.Maybe (fromMaybe)
import Data.String.CodeUnits as CodeUnits
import Effect (Effect)

hypothesis :: String
hypothesis = "toStringAs and fromStringAs with radixes plus xorshift bit operations; JS has them as builtins on doubles"

main :: Effect Unit
main = benchmark { size: 300000, workload }

workload :: Int -> String
workload n = do
  let random = foldl (\state _ -> xorshift state) 1463534242 (1 .. n)
  let text = foldl (\total i -> total + CodeUnits.length (toStringAs hexadecimal (mix i)) + CodeUnits.length (toStringAs binary (i .&. 1023))) 0 (1 .. n)
  let parsed = foldl (\total i -> total `xor` fromMaybe 0 (fromStringAs base36 (toStringAs base36 (mix i)))) 0 (1 .. n)
  show random <> " " <> show text <> " " <> show parsed
  where
  xorshift state = do
    let a = state `xor` (state `shl` 13)
    let b = a `xor` (a `shr` 17)
    b `xor` (b `shl` 5)
  mix i = ((i * -1640531535) `zshr` 3) .|. complement (i .&. 255)
  base36 = fromMaybe hexadecimal (radix 36)
