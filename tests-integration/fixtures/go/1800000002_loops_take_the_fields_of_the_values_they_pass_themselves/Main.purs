module Main where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.String.CodeUnits (toCharArray)
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Journal (log)

main :: Effect Unit
main = do
  log (show (sumJust 1000))
  log (show (fibonacci 40))
  log (show (spread [ 5, 3, 9, 1, 7 ]))
  log (show (runsIn "aaabbbcccaa"))
  log (show (runsIn ""))
  log (show (sumDown (Just 0) 100))
  log (show (sumDown Nothing 100))

sumJust :: Int -> Int
sumJust n = go (Just 0) 0
  where
  go acc i = case acc of
    Nothing -> 0
    Just s -> if i >= n then s else go (Just (s + i)) (i + 1)

fibonacci :: Int -> Int
fibonacci n = go (0 /\ 1) n
  where
  go (a /\ b) k = if k <= 0 then a else go (b /\ (a + b)) (k - 1)

spread :: Array Int -> Int
spread xs = go { low: 1000000, high: 0 } 0
  where
  go state i = case Array.index xs i of
    Nothing -> state.high - state.low
    Just x -> go { low: min state.low x, high: max state.high x } (i + 1)

data Mode = Fresh | InRun Char Int

runsIn :: String -> Int
runsIn text = go Fresh 0 0
  where
  chars = toCharArray text
  go mode runs i = case Array.index chars i of
    Nothing -> runs
    Just c -> case mode of
      Fresh -> go (InRun c 1) (runs + 1) (i + 1)
      InRun d k
        | c == d -> go (InRun d (k + 1)) runs (i + 1)
        | otherwise -> go (InRun c 1) (runs + 1) (i + 1)

sumDown :: Maybe Int -> Int -> Int
sumDown acc n = case acc of
  Nothing -> n
  Just s -> if n <= 0 then s else sumDown (Just (s + n)) (n - 1)
