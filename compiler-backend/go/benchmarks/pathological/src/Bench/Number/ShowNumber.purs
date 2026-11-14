module Bench.Number.ShowNumber where

import Prelude

import Bench.Harness (benchmark)
import Data.Array ((..))
import Data.Foldable (foldl)
import Data.Int (toNumber)
import Data.String.CodeUnits as CodeUnits
import Effect (Effect)

hypothesis :: String
hypothesis = "show on Number needs JS's shortest round-trip formatting; Go's strconv is fast but the JS exponent and integer rules need post-processing"

main :: Effect Unit
main = benchmark { size: 300000, workload }

workload :: Int -> String
workload n = do
  let total = foldl (\count i -> count + CodeUnits.length (show (number i))) 0 (1 .. n)
  show total <> " " <> show (number 7) <> " " <> show (number 300001) <> " " <> show (1.0e21 * toNumber n) <> " " <> show (1.0e-7 / toNumber n)
  where
  number i = case i `mod` 4 of
    0 -> toNumber i / 7.0
    1 -> toNumber i * 1.0e15
    2 -> toNumber i
    _ -> 1.0 / toNumber (i * i)
