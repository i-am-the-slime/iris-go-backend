module Main where

import Prelude

import Data.Array (filter, (..))
import Data.Foldable (for_)
import Effect (Effect)
import Effect.Ref as Ref

largeQuotient :: Int -> Int -> Boolean
largeQuotient n d = d /= 0 && n / d > 3

exactQuotient :: Int -> Int -> Boolean
exactQuotient n d = d /= 0 && n `mod` d == 0 && n / d > 1

checked :: Int -> Int -> Boolean
checked n d
  | d == 0 = false
  | n / d > 3 = true
  | otherwise = n `mod` d == 1

classify :: Int -> Int -> String
classify n d
  | d == 0 = "undefined"
  | n `mod` d == 0 = "divides"
  | n / d > 2 = "large"
  | otherwise = "small"

quotientOr :: Int -> Int -> Int
quotientOr n d = if d /= 0 && n / d > 3 then n / d else -1

remainderOr :: Int -> Int -> Int
remainderOr n d = case d of
  0 -> 0
  _
    | n `mod` d > 1 -> n `mod` d
    | otherwise -> n / d

divisible :: Int -> Array Int -> Array Int
divisible d = filter (\n -> d /= 0 && n `mod` d == 0 && n / d > 1)

naturalLarge :: Int -> Int -> Boolean
naturalLarge n d = n >= 0 && d > 0 && n / d > 3

naturalChecked :: Int -> Int -> Boolean
naturalChecked n d
  | n < 0 || d <= 0 = false
  | n / d > 3 = true
  | otherwise = n `mod` d == 1

naturalDivisible :: Int -> Array Int -> Array Int
naturalDivisible d = filter (\n -> d > 0 && n `mod` d == 0 && n / d > 1)

countedRemainders :: Int -> Int
countedRemainders n = go 0 0
  where
  go i total
    | i >= n = total
    | i > 2 && 100 / (i - 2) > 3 = go (i + 1) (total + 100 `mod` (i - 2))
    | otherwise = go (i + 1) (total + 1)

countedLarge :: Int -> Int
countedLarge n = go 0 0
  where
  go i total
    | i >= n = total
    | otherwise = go (i + 1) (total + if large i then 1 else 0)
  large i
    | i <= 2 = false
    | 100 / (i - 2) > 3 = true
    | otherwise = 100 `mod` (i - 2) == 1

main :: Effect Unit
main = do
  output <- Ref.new []
  let log line = Ref.modify_ (_ <> [ line ]) output
  inputs <- Ref.new { n: 17, divisors: [ 0, 4, 5, -3 ] }
  { n, divisors } <- Ref.read inputs
  log (show [ countedRemainders (n + 23), countedLarge (n + 23) ])
  for_ divisors \d -> do
    log (show [ largeQuotient n d, exactQuotient n d, checked n d ])
    log (classify n d <> " " <> show (quotientOr n d) <> " " <> show (remainderOr n d))
    log (show (divisible d (1 .. n)))
    log (show [ naturalLarge n d, naturalChecked n d ])
    log (show (naturalDivisible d (1 .. n)))
    when (d /= 0) do
      log ("quotient " <> show (n / d) <> " remainder " <> show (n `mod` d))
    when (d /= 0 && n / d > 3) do
      log "more than three"
    when (n >= 0 && d > 0) do
      log ("natural quotient " <> show (n / d) <> " remainder " <> show (n `mod` d))
