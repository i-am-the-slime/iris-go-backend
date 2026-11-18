module Compat.Exotic.Ranges where

import Prelude

import Data.Array (all, any, concatMap, filter, findIndex, findLastIndex, foldl, foldr, length, mapWithIndex, (..))
import Data.Foldable (for_, sum, traverse_)
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Effect.Console (log)
import Effect.Ref as Ref

main :: Effect Unit
main = do
  for_ bounds \(first /\ last) -> log (summary first last)
  for_ (0 .. 3) \i -> log ("for_ " <> show i)
  for_ (2 .. (-1)) \i -> log ("descending for_ " <> show i)
  traverse_ (\i -> log ("traverse_ " <> show i)) (map (_ * 10) (1 .. 3))
  counter <- Ref.new 0
  for_ (1 .. 4) \i -> Ref.modify_ (\total -> total * 10 + i) counter
  Ref.read counter >>= \total -> log ("effects in order " <> show total)
  log (show (map (\thunk -> thunk unit) (map (\i -> \_ -> i * i) (3 .. 0))))
  where
  bounds =
    [ 1 /\ 5, 1 /\ 0, 1 /\ 1, 5 /\ 1, -3 /\ 3, 0 /\ (-4)
    , (top - 2) /\ top, top /\ (top - 2), bottom /\ (bottom + 2), (bottom + 2) /\ bottom
    ]

summary :: Int -> Int -> String
summary first last = show
  { first
  , last
  , summed: foldl (+) 0 (first .. last)
  , counted: foldl (\count _ -> count + 1) 0 (first .. last)
  , listed: foldr (\x rest -> show x <> "," <> rest) "" (first .. last)
  , doubled: map (_ * 2) (first .. last)
  , indexed: mapWithIndex (\index x -> index * 100 + x) (first .. last)
  , odd: filter (\x -> x `mod` 2 /= 0) (first .. last)
  , anyAboveTwo: any (_ > 2) (first .. last)
  , allAboveZero: all (_ > 0) (first .. last)
  , firstEven: findIndex (\x -> x `mod` 2 == 0) (first .. last)
  , lastEven: findLastIndex (\x -> x `mod` 2 == 0) (first .. last)
  , length: length (first .. last)
  , lengthOfOdd: length (filter (\x -> x `mod` 2 /= 0) (first .. last))
  , sum: sum (map (_ * 3) (first .. last))
  , nested: foldl (+) 0 (concatMap (\x -> x .. last) (first .. last))
  }
