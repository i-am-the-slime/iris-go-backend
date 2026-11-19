module Bench.Idiom.STArray.QuickSort where

import Prelude

import Bench.Harness (benchmark)
import Bench.Idiom.Random (pseudoRandomArray)
import Control.Monad.ST (ST, for, run)
import Control.Monad.ST.Ref as STRef
import Data.Array as Array
import Data.Array.ST (STArray)
import Data.Array.ST as STArray
import Data.Foldable (foldl)
import Data.Maybe (fromMaybe)
import Effect (Effect)

idiom :: String
idiom = "in-place quicksort in withArray: recursive ST action, Lomuto partition as a for loop over peek and poke with an STRef boundary"

main :: Effect Unit
main = benchmark { size: 400000, workload }

workload :: Int -> String
workload n = do
  let sorted = run (STArray.withArray quickSort (pseudoRandomArray n))
  show (foldl (+) 0 sorted) <> " " <> show (fromMaybe 0 (Array.index sorted (n / 2)))

quickSort :: forall region. STArray region Int -> ST region Unit
quickSort array = do
  size <- STArray.length array
  sortRange 0 (size - 1)
  where
  peekOrZero i = map (fromMaybe 0) (STArray.peek i array)

  swap i j = do
    x <- peekOrZero i
    y <- peekOrZero j
    _ <- STArray.poke i y array
    void (STArray.poke j x array)

  sortRange low high = when (low < high) do
    pivot <- peekOrZero high
    boundary <- partition pivot low high
    swap boundary high
    sortRange low (boundary - 1)
    sortRange (boundary + 1) high

  partition pivot low high = do
    boundary <- STRef.new low
    for low high \j -> do
      x <- peekOrZero j
      when (x < pivot) do
        b <- STRef.read boundary
        swap b j
        void (STRef.write (b + 1) boundary)
    STRef.read boundary
