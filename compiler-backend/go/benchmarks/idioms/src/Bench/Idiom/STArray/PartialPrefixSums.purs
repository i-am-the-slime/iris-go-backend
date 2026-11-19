module Bench.Idiom.STArray.PartialPrefixSums where

import Prelude

import Bench.Harness (benchmark)
import Bench.Idiom.Random (pseudoRandomArray)
import Control.Monad.ST (ST, for, run)
import Data.Array as Array
import Data.Array.ST (STArray)
import Data.Array.ST as STArray
import Data.Array.ST.Partial as Partial
import Data.Maybe (fromMaybe)
import Effect (Effect)
import Partial.Unsafe (unsafePartial)

idiom :: String
idiom = "prefix sums in withArray through Data.Array.ST.Partial: the same loop as PrefixSums with peek and poke that skip the bounds check and the Maybe"

main :: Effect Unit
main = benchmark { size: 4000000, workload }

workload :: Int -> String
workload n = do
  let sums = run (STArray.withArray prefixSums (pseudoRandomArray n))
  show (fromMaybe 0 (Array.last sums)) <> " " <> show (fromMaybe 0 (Array.index sums (n / 2)))

prefixSums :: forall region. STArray region Int -> ST region Unit
prefixSums array = do
  size <- STArray.length array
  for 1 size \i -> unsafePartial do
    previous <- Partial.peek (i - 1) array
    current <- Partial.peek i array
    Partial.poke i (previous + current) array
