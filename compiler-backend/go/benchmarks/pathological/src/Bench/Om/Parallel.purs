module Bench.Om.Parallel where

import Prelude

import Bench.Harness (benchmarkAff)
import Data.Array ((..))
import Data.Foldable (sum)
import Effect (Effect)
import Effect.Aff (Aff)
import Yoga.Om (Om, ask)
import Yoga.Om as Om

hypothesis :: String
hypothesis = "each ParOm apply supervises two forked fibers that meet through two AVars, so inParallel and race over small tasks are dominated by fiber and AVar handoffs in the Aff scheduler"

main :: Effect Unit
main = benchmarkAff { size: 2000, workload }

type Config = { factor :: Int }

workload :: Int -> Aff String
workload n = Om.runOm { factor: 3 } { exception: \_ -> pure "exception", rejected: \i -> pure ("rejected " <> show i) } do
  products <- Om.inParallel (map scaled (1 .. n))
  winners <- Om.inParallel (map contest (1 .. (n / 4)))
  pure (show (sum products) <> " " <> show (sum winners))
  where
  scaled :: Int -> Om Config (rejected :: Int) Int
  scaled i = do
    { factor } <- ask
    pure ((i * factor) `mod` 1009)

  contest :: Int -> Om Config (rejected :: Int) Int
  contest i = Om.race [ Om.throw { rejected: i }, scaled i ]
