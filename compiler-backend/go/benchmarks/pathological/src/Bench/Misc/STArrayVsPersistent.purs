module Bench.Misc.STArrayVsPersistent where

import Prelude

import Bench.Harness (benchmark)
import Control.Monad.ST (ST, run, for)
import Data.Array ((..))
import Data.Array as Array
import Data.Array.ST (STArray)
import Data.Array.ST as STArray
import Data.Foldable (foldl, sum)
import Data.Maybe (fromMaybe)

import Effect (Effect)

hypothesis :: String
hypothesis = "Data.Array.ST push, peek and poke against a persistent snoc loop: the ST side is a tight loop in both, the persistent side copies quadratically in both"

main :: Effect Unit
main = benchmark { size: 400000, workload }

workload :: Int -> String
workload n = do
  let mutable = run (buildMutable n)
  let persistent = foldl Array.snoc [] (1 .. (n / 100))
  show (sum mutable) <> " " <> show (Array.length mutable) <> " " <> show (sum persistent)

buildMutable :: forall region. Int -> ST region (Array Int)
buildMutable n = do
  array <- STArray.new
  for 0 n \i -> void (STArray.push (i `mod` 1000) array)
  for 1 n \i -> do
    previous <- STArray.peek (i - 1) array
    void (STArray.modify i (_ + fromMaybe 0 previous `mod` 7) array)
  STArray.unsafeFreeze array

_proof :: forall region. STArray region Int -> STArray region Int
_proof = identity
