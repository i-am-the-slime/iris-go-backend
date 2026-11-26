module Main where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl)

data Operation = Add Int | Skip

main :: Int
main = totals.total + totals.steps
  where
  operations = Array.range 1 1000 <#> \n -> if n `mod` 3 == 0 then Skip else Add n
  totals = operations # foldl perform { total: 0, steps: 0 }
  perform { total, steps } = case _ of
    Add n -> { total: total + n, steps: steps + 1 }
    Skip -> { total, steps: steps + 1 }
