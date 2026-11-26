module Main where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Map (Map)
import Data.Map as Map

type State = { clock :: Int, byKey :: Map Int Int }

tick :: State -> Int -> State
tick state key = state { clock = state.clock + 1, byKey = Map.insert key state.clock state.byKey }

remember :: Int -> State -> State
remember key state = state { clock = state.clock + 1, byKey = Map.insert key state.clock state.byKey }

forget :: Int -> State -> State
forget key state = state { byKey = Map.delete key state.byKey }

step :: State -> Int -> State
step state key
  | key `mod` 3 == 0 = remember key (forget (key - 1) state)
  | otherwise = remember key state

main :: Int
main = ticked.clock + Map.size ticked.byKey + Map.size stepped.byKey
  where
  keys = Array.range 1 2000 <#> (_ `mod` 50)
  ticked = keys # foldl tick { clock: 0, byKey: Map.empty }
  stepped = keys # foldl step { clock: 0, byKey: Map.empty }
