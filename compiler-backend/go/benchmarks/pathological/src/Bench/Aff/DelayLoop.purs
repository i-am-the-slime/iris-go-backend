module Bench.Aff.DelayLoop where

import Prelude

import Bench.Harness (benchmarkAff)
import Effect (Effect)
import Effect.Aff (Aff, delay)
import Data.Time.Duration (Milliseconds(..))

hypothesis :: String
hypothesis = "delay (Milliseconds 0.0) yields to the event loop; JS timers have a 1 ms floor, Go wakes through the runtime timer heap"

main :: Effect Unit
main = benchmarkAff { size: 1000, workload }

workload :: Int -> Aff String
workload n = loop 0 0
  where
  loop i accumulated
    | i >= n = pure (show accumulated)
    | otherwise = do
        delay (Milliseconds 0.0)
        loop (i + 1) (accumulated + i)
