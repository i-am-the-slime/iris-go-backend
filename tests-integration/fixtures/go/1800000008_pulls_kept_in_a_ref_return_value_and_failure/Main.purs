module Main where

import Prelude

import Cell (Cell)
import Cell as Cell
import Data.Either (Either(..), either)
import Effect (Effect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Journal (log)

type Pull = Unit -> Effect (Either String Int)

countingTo :: Int -> Ref Int -> Pull
countingTo limit counter _ = do
  count <- Ref.modify (_ + 1) counter
  pure if count > limit then Left ("past " <> show limit) else Right count

pullThrough :: Cell Pull -> Int -> Effect (Either String Int)
pullThrough current total = do
  pull <- Cell.read current
  pulled <- pull unit
  case pulled of
    Left problem -> pure (if total > 20 then Right total else Left problem)
    Right count
      | count == 3 -> do
          counter <- Ref.new 10
          Cell.write current (countingTo 12 counter)
          pullThrough current (total + count)
      | otherwise -> pullThrough current (total + count)

main :: Effect Unit
main = do
  counter <- Ref.new 0
  current <- Cell.new (countingTo 5 counter)
  pullThrough current 0 >>= either ("failed: " <> _) show >>> log
