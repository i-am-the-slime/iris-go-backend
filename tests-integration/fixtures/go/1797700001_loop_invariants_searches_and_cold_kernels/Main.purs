module Main where

import Prelude

import Data.Array (concatMap, filter, find, length, (..))
import Data.Foldable (foldl)
import Data.Int (toNumber)
import Data.Maybe (Maybe(..), fromMaybe)

-- | `find` stops at the element it finds, so the `map` before it runs in its loop.
firstEven :: Array Int -> Maybe Int
firstEven numbers = find (\n -> n `mod` 2 == 0) (map (_ + 1) numbers)

firstLong :: Array String -> Maybe String
firstLong words = find (\word -> word > "w5") (map (_ <> "!") words)

-- | A `map` keeps the length of what it maps, so counting it builds nothing.
average :: Int -> Number
average size = do
  let scaled = map (\x -> toNumber x * 0.5) (1 .. size)
  foldl (+) 0.0 scaled / toNumber (length scaled)

-- | Clamps between ordered constants are Go's `min` and `max` in a kernel's scalar loop.
clamped :: Array Int -> Array Int
clamped = map \x -> if x < 2 then 2 else if x > 40 then 40 else x

atLeastSeven :: Array Int -> Array Int
atLeastSeven = map \x -> if x > 7 then x else 7

type Rule = { name :: String, check :: Int -> Boolean }

-- | Ranges and literals a loop never changes are built once, before it.
checks :: Int -> Array String
checks limit = concatMap (\n -> map _.name (filter (\rule -> rule.check n) rules)) (0 .. 4)
  where
  rules :: Array Rule
  rules =
    [ { name: "positive", check: \n -> n > 0 }
    , { name: "small", check: \n -> n < limit }
    ]

placements :: Int -> Array (Array Int) -> Array (Array Int)
placements size placed = concatMap (\queens -> map (\row -> [ row ] <> queens) (1 .. size)) placed

main :: Array String
main = do
  let numbers = 0 .. 40
  [ show (firstEven numbers), show (firstLong (map show numbers)), show (average 41)
  , show (clamped numbers), show (checks 3), show (length (placements 3 [ [ 1 ], [ 2 ] ]))
  ]
    <> ([ 1, 2 ] >>= \round -> [ show (clamped (map (_ * round) numbers)), show (atLeastSeven numbers) ])
