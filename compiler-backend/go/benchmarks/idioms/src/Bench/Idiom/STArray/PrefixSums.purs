module Bench.Idiom.STArray.PrefixSums where

import Prelude

import Bench.Harness (benchmark)
import Bench.Idiom.Random (pseudoRandomArray)
import Control.Monad.ST (ST, for, run)
import Data.Array as Array
import Data.Array.ST (STArray)
import Data.Array.ST as STArray
import Data.Maybe (fromMaybe)
import Effect (Effect)

idiom :: String
idiom = "prefix sums in withArray: Control.Monad.ST.for reading two elements with peek (a Maybe each) and writing one with poke"

main :: Effect Unit
main = benchmark { size: 4000000, workload }

workload :: Int -> String
workload n = do
  let sums = run (STArray.withArray prefixSums (pseudoRandomArray n))
  show (fromMaybe 0 (Array.last sums)) <> " " <> show (fromMaybe 0 (Array.index sums (n / 2)))

prefixSums :: forall region. STArray region Int -> ST region Unit
prefixSums array = do
  size <- STArray.length array
  for 1 size \i -> do
    previous <- STArray.peek (i - 1) array
    current <- STArray.peek i array
    void (STArray.poke i (fromMaybe 0 previous + fromMaybe 0 current) array)
