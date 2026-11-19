module Bench.Idiom.STRef.Counters where

import Prelude

import Bench.Harness (benchmark)
import Bench.Idiom.Random (pseudoRandomArray)
import Control.Monad.ST (ST, for, foreach, run, while)
import Control.Monad.ST.Ref as STRef
import Data.Int.Bits (and)
import Effect (Effect)

idiom :: String
idiom = "STRef counters: for with modify, while over a read index with write, and foreach over an array"

main :: Effect Unit
main = benchmark { size: 10000000, workload }

workload :: Int -> String
workload n = show (run (counters n))

counters :: forall region. Int -> ST region Int
counters n = do
  total <- STRef.new 0
  for 0 n \i -> void (STRef.modify (_ + (i `and` 7)) total)
  index <- STRef.new 0
  while (map (_ < n) (STRef.read index)) do
    i <- STRef.read index
    _ <- STRef.modify (_ + (i `mod` 3)) total
    void (STRef.write (i + 1) index)
  foreach (pseudoRandomArray (n / 10)) \x -> void (STRef.modify (_ + (x `and` 1)) total)
  STRef.read total
