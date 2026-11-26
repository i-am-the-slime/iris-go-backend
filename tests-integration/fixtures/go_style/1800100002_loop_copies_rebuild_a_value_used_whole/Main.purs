module Main where

import Prelude

import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Console (log)

main :: Effect Unit
main = do
  log (summedUpTo 1000)
  log (show (stepsBelow 10 (Just 0) 0))

summedUpTo :: Int -> String
summedUpTo limit = go (Just 0) 0
  where
  go current total = case current of
    Nothing -> "none"
    Just n
      | n >= limit -> show total <> " at " <> show current
      | otherwise -> go (Just (n + 1)) (total + n)

stepsBelow :: Int -> Maybe Int -> Int -> Array (Maybe Int)
stepsBelow limit current steps = case current of
  Nothing -> []
  Just n
    | n >= limit -> [ current, Just steps ]
    | otherwise -> stepsBelow limit (Just (n + 2)) (steps + 1)
