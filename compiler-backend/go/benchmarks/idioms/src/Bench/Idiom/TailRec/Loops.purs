module Bench.Idiom.TailRec.Loops where

import Prelude

import Bench.Harness (benchmark)
import Control.Monad.Rec.Class (Step(..), tailRec, tailRecM)
import Control.Monad.ST (ST, run)
import Control.Monad.ST.Ref as STRef
import Effect (Effect)

idiom :: String
idiom = "Control.Monad.Rec.Class: tailRec with a record state over a nested Euclid loop, and tailRecM in ST accumulating into an STRef"

main :: Effect Unit
main = benchmark { size: 2000000, workload }

workload :: Int -> String
workload n = show (greatestDivisors n) <> " " <> show (run (countUp n))

greatestDivisors :: Int -> Int
greatestDivisors n = tailRec outer { i: 1, total: 0 }
  where
  outer { i, total }
    | i > n = Done total
    | otherwise = Loop { i: i + 1, total: total + euclid i (n + 1 - i) }

  euclid a b = tailRec inner { a, b }

  inner { a, b }
    | b == 0 = Done a
    | otherwise = Loop { a: b, b: a `mod` b }

countUp :: forall region. Int -> ST region Int
countUp n = do
  total <- STRef.new 0
  tailRecM (step total) 1
  STRef.read total
  where
  step total i
    | i > n = pure (Done unit)
    | otherwise = do
        _ <- STRef.modify (_ + (i `mod` 7)) total
        pure (Loop (i + 1))
