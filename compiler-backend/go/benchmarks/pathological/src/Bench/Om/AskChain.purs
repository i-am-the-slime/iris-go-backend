module Bench.Om.AskChain where

import Prelude

import Bench.Harness (benchmarkAff)
import Effect (Effect)
import Effect.Aff (Aff)
import Yoga.Om (Om, ask, asks)
import Yoga.Om as Om

hypothesis :: String
hypothesis = "every Om bind runs RWSET's six-argument CPS with a trampoline thunk per step, and ask/asks read the context record through the same machinery"

type Config = { step :: Int, modulus :: Int, offset :: Int, label :: String }

main :: Effect Unit
main = benchmarkAff { size: 100000, workload }

workload :: Int -> Aff String
workload n = loop 0 0 # Om.runOm config { exception: \_ -> pure "exception" }
  where
  config = { step: 3, modulus: 1000003, offset: 7, label: "acc" }

  loop :: Int -> Int -> Om Config () String
  loop i accumulated
    | i >= n = render accumulated
    | otherwise = do
        { step } <- ask
        modulus <- asks _.modulus
        next <- addOffset (accumulated * step + i)
        loop (i + 1) (next `mod` modulus)

  addOffset :: Int -> Om Config () Int
  addOffset x = do
    { offset } <- ask
    pure (x + offset)

  render :: Int -> Om Config () String
  render accumulated = asks \{ label } -> label <> "=" <> show accumulated
