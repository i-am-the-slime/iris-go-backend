module Bench.Idiom.Ref.EffectLoops where

import Prelude

import Bench.Harness (benchmarkEffect)
import Bench.Idiom.Random (pseudoRandomArray)
import Control.Monad.Rec.Class (Step(..), tailRecM)
import Data.Int.Bits (and)
import Effect (Effect, forE, foreachE, whileE)
import Effect.Ref as Ref

idiom :: String
idiom = "Effect.Ref counters: forE with modify_, whileE over a read index with write, foreachE over an array, and tailRecM in Effect"

main :: Effect Unit
main = benchmarkEffect { size: 10000000, workload }

workload :: Int -> Effect String
workload n = do
  total <- Ref.new 0
  forE 0 n \i -> Ref.modify_ (_ + (i `and` 7)) total
  index <- Ref.new 0
  whileE (map (_ < n) (Ref.read index)) do
    i <- Ref.read index
    Ref.modify_ (_ + (i `mod` 3)) total
    Ref.write (i + 1) index
  foreachE (pseudoRandomArray (n / 10)) \x -> Ref.modify_ (_ + (x `and` 1)) total
  tailRecM (countUp total) 0
  show <$> Ref.read total
  where
  countUp total i
    | i >= n = pure (Done unit)
    | otherwise = do
        Ref.modify_ (_ + (i `and` 1)) total
        pure (Loop (i + 1))
