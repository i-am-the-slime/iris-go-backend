module Main where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))

type Tally = { total :: Int, byKey :: Map Int Int }

-- | Counts the keys from a position on, answering how many times they were seen before.
countFrom :: Array Int -> Int -> Int -> Tally -> Tuple Int Tally
countFrom keys position seen tally = case Array.index keys position of
  Nothing -> Tuple seen tally
  Just key -> do
    let before = case Map.lookup key tally.byKey of
          Nothing -> 0
          Just times -> times
    countFrom keys (position + 1) (seen + before) tally { total = tally.total + 1, byKey = Map.insert key (before + 1) tally.byKey }

main :: Int
main = looped.repeats + Map.size looped.tally.byKey + twice
  where
  looped = Array.range 1 200 <#> (_ `mod` 30) # foldl step { tally: { total: 0, byKey: Map.empty }, repeats: 0 }
  step state key = case countFrom [ key, key + 1 ] 0 0 state.tally of
    Tuple seen tally -> { tally, repeats: state.repeats + seen }
  start = case countFrom [ 1, 2, 3 ] 0 0 { total: 0, byKey: Map.empty } of
    Tuple _ tally -> tally
  twice = case countFrom [ 1 ] 0 0 start, countFrom [ 1, 2 ] 0 0 start of
    Tuple first _, Tuple second _ -> first * 10 + second
