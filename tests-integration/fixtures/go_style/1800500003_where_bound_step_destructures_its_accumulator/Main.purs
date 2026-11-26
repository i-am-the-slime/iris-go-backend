module Main where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl)
import Effect (Effect)
import Effect.Console (logShow)

data Operation = Add Int | Skip

main :: Effect Unit
main = do
  logShow totals.total
  logShow totals.steps
  logShow (Array.range 1 5 # foldl (pair 10) { left: 0, right: [] }).right
  where
  operations = Array.range 1 1000 <#> \n -> if n `mod` 3 == 0 then Skip else Add n
  totals = operations # foldl perform { total: 0, steps: 0 }
  perform { total, steps } = case _ of
    Add n -> { total: total + n, steps: steps + 1 }
    Skip -> { total, steps: steps + 1 }
  pair offset { left, right } = \n -> { left: left + n, right: Array.snoc right (offset + left) }
