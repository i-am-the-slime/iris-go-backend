module Bench.Idiom.STArray.PushIterate where

import Prelude

import Bench.Harness (benchmark)
import Bench.Idiom.Random (xorshift)
import Control.Monad.ST (ST, for, run)
import Control.Monad.ST.Ref as STRef
import Data.Array as Array
import Data.Array.ST as STArray
import Data.Array.ST.Iterator as Iterator
import Data.Int.Bits (and)
import Effect (Effect)

idiom :: String
idiom = "build with new and push in a for loop, modify every element, freeze a snapshot, then sum it through Data.Array.ST.Iterator into an STRef"

main :: Effect Unit
main = benchmark { size: 2000000, workload }

workload :: Int -> String
workload n = show (run (build n))

build :: forall region. Int -> ST region Int
build n = do
  array <- STArray.new
  for 0 n \i -> void (STArray.push (xorshift (i + 1)) array)
  for 0 n \i -> void (STArray.modify i (_ `and` 0xFFFF) array)
  snapshot <- STArray.freeze array
  total <- STRef.new 0
  iterator <- Iterator.iterator (Array.index snapshot)
  Iterator.iterate iterator \x -> void (STRef.modify (_ + x) total)
  STRef.read total
