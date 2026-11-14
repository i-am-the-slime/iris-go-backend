module Bench.Number.Parse where

import Prelude

import Bench.Harness (benchmark)
import Data.Array ((..))
import Data.Foldable (foldl)
import Data.Int as Int
import Data.Maybe (fromMaybe)
import Data.Number as Number
import Effect (Effect)

hypothesis :: String
hypothesis = "Number.fromString and Int.fromString in a loop: JS parses natively, Go must replicate parseFloat's prefix rules and JS Int range checks"

main :: Effect Unit
main = benchmark { size: 300000, workload }

workload :: Int -> String
workload n = do
  let numbers = foldl (\total i -> total + fromMaybe 0.0 (Number.fromString (numberText i))) 0.0 (1 .. n)
  let ints = foldl (\total i -> total + fromMaybe 1 (Int.fromString (intText i))) 0 (1 .. n)
  show numbers <> " " <> show ints
  where
  numberText i = case i `mod` 4 of
    0 -> show i <> ".25"
    1 -> "  " <> show i <> "e-3"
    2 -> "-" <> show i <> ".5abc"
    _ -> "nope"
  intText i = case i `mod` 3 of
    0 -> show (i `mod` 1000)
    1 -> "-" <> show (i `mod` 977)
    _ -> "99999999999"
