module Main where

import Prelude

import Data.Foldable (foldl)
import Effect (Effect)
import Effect.Ref as Ref

type Run = { matches :: Int, before :: Int, total :: Int }

countAlong :: Array Boolean -> Int
countAlong matches = (foldl step { matches: 0, before: 0, total: 0 } matches).total
  where
  step run same
    | same = run { matches = run.matches + 1, total = run.total + run.before }
    | otherwise = do
        let starts = run.matches + 1
        { matches: 0, before: starts, total: run.total + starts }

type Bounds = { low :: Int, high :: Int }

differing :: Array Int -> Int
differing xs = (foldl step { low: 0, high: 0 } xs).high
  where
  step bounds x
    | x < 3 = bounds { low = bounds.low + x, high = bounds.high + bounds.low }
    | otherwise = { low: bounds.low - 1, high: bounds.high + bounds.low * 2 }

main :: Effect Unit
main = do
  output <- Ref.new []
  matches <- Ref.new [ true, false, true, true, false, true ]
  numbers <- Ref.new [ 1, 5, 2, 7, 0 ]
  counted <- countAlong <$> Ref.read matches
  bounded <- differing <$> Ref.read numbers
  Ref.write [ counted, bounded ] output
