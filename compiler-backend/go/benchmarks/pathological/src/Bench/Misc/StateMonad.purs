module Bench.Misc.StateMonad where

import Prelude

import Bench.Harness (benchmark)
import Control.Monad.State (State, execState, get, modify_, put)
import Data.Array ((..))
import Data.Foldable (foldl, for_)
import Effect (Effect)

hypothesis :: String
hypothesis = "for_ over StateT Identity: every step allocates a state-threading closure and a tuple"

main :: Effect Unit
main = benchmark { size: 300000, workload }

workload :: Int -> String
workload n = do
  let final = foldl (\state _ -> execState (program 2000) state) { count: 0, sum: 0, last: 0 } (1 .. (n / 2000))
  show final.count <> " " <> show final.sum <> " " <> show final.last
  where
  program :: Int -> State { count :: Int, sum :: Int, last :: Int } Unit
  program size = for_ (1 .. size) \i -> do
    state <- get
    when (i `mod` 3 /= 0) (put state { count = state.count + 1 })
    modify_ \s -> s { sum = (s.sum + i) `mod` 1000003, last = i }
