module Bench.Aff.ForkJoin where

import Prelude

import Bench.Harness (benchmarkAff)
import Data.Array ((..))
import Data.Foldable (sum)
import Data.Traversable (traverse)
import Effect (Effect)
import Effect.Aff (Aff, forkAff, joinFiber)

hypothesis :: String
hypothesis = "thousands of forkAff + joinFiber: JS fibers are plain objects on one thread, Go fibers go through a scheduler and synchronisation"

main :: Effect Unit
main = benchmarkAff { size: 20000, workload }

workload :: Int -> Aff String
workload n = do
  fibers <- traverse (\i -> forkAff (work i)) (1 .. n)
  results <- traverse joinFiber fibers
  nested <- forkAff (traverse (\i -> forkAff (work i) >>= joinFiber) (1 .. (n / 4))) >>= joinFiber
  pure (show (sum results) <> " " <> show (sum nested))
  where
  work i = pure ((i * i) `mod` 1009)
