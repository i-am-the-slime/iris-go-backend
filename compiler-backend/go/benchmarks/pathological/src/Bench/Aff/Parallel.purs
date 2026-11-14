module Bench.Aff.Parallel where

import Prelude

import Bench.Harness (benchmarkAff)
import Control.Parallel (parTraverse, parallel, sequential)
import Data.Array ((..))
import Data.Foldable (sum)
import Effect (Effect)
import Effect.Aff (Aff)

hypothesis :: String
hypothesis = "parTraverse and parallel/sequential build ParAff trees that the JS interpreter runs in one loop; Go runs them through its fiber machinery"

main :: Effect Unit
main = benchmarkAff { size: 20000, workload }

workload :: Int -> Aff String
workload n = do
  squares <- parTraverse (\i -> pure ((i * i) `mod` 1009)) (1 .. n)
  pairs <- parTraverse (\i -> sequential ((+) <$> parallel (pure i) <*> parallel (pure (i * 2)))) (1 .. (n / 2))
  pure (show (sum squares) <> " " <> show (sum pairs))
