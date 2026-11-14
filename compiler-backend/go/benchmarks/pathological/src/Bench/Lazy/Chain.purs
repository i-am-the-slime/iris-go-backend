module Bench.Lazy.Chain where

import Prelude

import Bench.Harness (benchmark)
import Data.Array ((..))
import Data.Foldable (foldl)
import Data.Lazy (Lazy, defer, force)
import Effect (Effect)

hypothesis :: String
hypothesis = "Data.Lazy chains allocate a thunk and a closure per link and force recursively; short-lived thunks are V8's best case"

main :: Effect Unit
main = benchmark { size: 900, workload }

workload :: Int -> String
workload n = show (foldl (\total i -> (total + force (chain i)) `mod` 1000003) 0 (1 .. n))
  where
  chain :: Int -> Lazy Int
  chain seed = foldl link (defer \_ -> seed) (1 .. 1000)

  link :: Lazy Int -> Int -> Lazy Int
  link previous i = map (\value -> (value * 3 + i) `mod` 1000003) (defer \_ -> force previous)
