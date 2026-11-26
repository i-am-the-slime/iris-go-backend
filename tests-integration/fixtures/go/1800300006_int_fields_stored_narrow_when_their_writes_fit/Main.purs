module Main where

import Prelude

import Data.Int as Int
import Data.Maybe (fromMaybe)
import Effect (Effect)
import Journal (log)

data Ladder = Rung Int Int Ladder | Ground

data Tally = Tally Int Tally | Done

data Span = Span Int Span | Closed

main :: Effect Unit
main = do
  let ladder = climb 100
  log (show (spread ladder))
  log (show (spread (swapped ladder)))
  log (show (counted (parsed "41")))
  log (show (measured (stretched 100)))

climb :: Int -> Ladder
climb = go Ground
  where
  go ladder n
    | n <= 0 = ladder
    | otherwise = go (Rung n (n * 3) ladder) (n - 1)

swapped :: Ladder -> Ladder
swapped = case _ of
  Rung low high rest -> Rung high low (swapped rest)
  Ground -> Ground

spread :: Ladder -> Int
spread = go 0
  where
  go total = case _ of
    Rung low high rest -> go (total + high - low) rest
    Ground -> total

parsed :: String -> Tally
parsed text = Tally number (Tally (number + 1) Done)
  where
  number = fromMaybe 0 (Int.fromString text)

counted :: Tally -> Int
counted = case _ of
  Tally count rest -> count + counted rest
  Done -> 0

stretched :: Int -> Span
stretched = go Closed
  where
  go span n
    | n <= 0 = span
    | otherwise = go (Span (n * 100000000) span) (n - 1)

measured :: Span -> Int
measured = go 0
  where
  go total = case _ of
    Span width rest -> go (total + width) rest
    Closed -> total
