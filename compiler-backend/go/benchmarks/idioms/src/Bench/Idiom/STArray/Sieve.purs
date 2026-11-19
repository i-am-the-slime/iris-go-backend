module Bench.Idiom.STArray.Sieve where

import Prelude

import Bench.Harness (benchmark)
import Control.Monad.ST (ST, for, run)
import Data.Array as Array
import Data.Array.ST (STArray)
import Data.Array.ST as STArray
import Data.Foldable (foldl)
import Data.Int as Int
import Data.Maybe (fromMaybe)
import Data.Number as Number
import Effect (Effect)

idiom :: String
idiom = "sieve of Eratosthenes: thaw a replicated array, Control.Monad.ST.for with peek and poke, unsafeFreeze, count with foldl"

main :: Effect Unit
main = benchmark { size: 8000000, workload }

workload :: Int -> String
workload n = show (foldl countTrue 0 (sieve n))
  where
  countTrue count flag = if flag then count + 1 else count

sieve :: Int -> Array Boolean
sieve n = run do
  flags <- STArray.thaw (Array.replicate (n + 1) true)
  _ <- STArray.poke 0 false flags
  _ <- STArray.poke 1 false flags
  for 2 (limit + 1) \i -> do
    isPrime <- STArray.peek i flags
    when (fromMaybe false isPrime) (clearMultiples i flags)
  STArray.unsafeFreeze flags
  where
  limit = Int.floor (Number.sqrt (Int.toNumber n))

  clearMultiples :: forall region. Int -> STArray region Boolean -> ST region Unit
  clearMultiples i flags = for 0 ((n - i * i) / i + 1) \k -> void (STArray.poke (i * i + k * i) false flags)
