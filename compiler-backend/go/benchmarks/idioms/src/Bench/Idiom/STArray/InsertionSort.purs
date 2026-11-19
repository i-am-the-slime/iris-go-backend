module Bench.Idiom.STArray.InsertionSort where

import Prelude

import Bench.Harness (benchmark)
import Bench.Idiom.Random (pseudoRandomArray)
import Control.Monad.ST (ST, for, run)
import Data.Array as Array
import Data.Array.ST (STArray)
import Data.Array.ST as STArray
import Data.Foldable (foldl)
import Data.Maybe (fromMaybe)
import Effect (Effect)

idiom :: String
idiom = "insertion sort in withArray: the inner shift loop is a tail-recursive ST action over peek and poke"

main :: Effect Unit
main = benchmark { size: 10000, workload }

workload :: Int -> String
workload n = do
  let sorted = run (STArray.withArray insertionSort (pseudoRandomArray n))
  show (foldl (+) 0 sorted) <> " " <> show (fromMaybe 0 (Array.index sorted (n / 2)))

insertionSort :: forall region. STArray region Int -> ST region Unit
insertionSort array = do
  size <- STArray.length array
  for 1 size \i -> do
    current <- peekOrZero i
    shiftDown current (i - 1)
  where
  peekOrZero i = map (fromMaybe 0) (STArray.peek i array)

  shiftDown current j
    | j < 0 = void (STArray.poke 0 current array)
    | otherwise = do
        previous <- peekOrZero j
        if previous > current then do
          _ <- STArray.poke (j + 1) previous array
          shiftDown current (j - 1)
        else void (STArray.poke (j + 1) current array)
