module Bench.String.ConcatLoop where

import Prelude

import Bench.Harness (benchmark)
import Data.Array ((..))
import Data.Foldable (foldl)
import Data.String.CodeUnits as CodeUnits
import Effect (Effect)

hypothesis :: String
hypothesis = "JS <> builds a rope in O(1); Go copies the accumulated string on every append"

main :: Effect Unit
main = benchmark { size: 100000, workload }

workload :: Int -> String
workload n = do
  let viaFold = foldl (\accumulated i -> accumulated <> show (i `mod` 10)) "" (1 .. n)
  let viaLoop = loop 0 ""
  show (CodeUnits.length viaFold) <> " " <> show (CodeUnits.length viaLoop) <> " " <> CodeUnits.take 20 viaLoop
  where
  loop i accumulated
    | i >= n = accumulated
    | otherwise = loop (i + 1) (accumulated <> "ab")
