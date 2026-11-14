module Main where

import Prelude

import Data.Array (head, index)
import Data.Maybe (Maybe(..), fromMaybe, maybe)

opaque :: Int -> Int
opaque x = if x == 12345 then opaque x else x

-- `map` and `fromMaybe` over a lookup never build a Maybe.
firstId :: Array { id :: String } -> String
firstId xs = fromMaybe "" (map _.id (head xs))

-- An index check against a literal index folds away.
second :: Array Int -> Int
second xs = maybe 0 (_ + 1) (index xs 1)

-- A choice between constructors with fields meets the case that takes them apart.
data Shape = Circle Int | Square Int Int

measure :: Int -> Int
measure n = case (if n > 0 then Circle (opaque n) else Square (opaque n) 2) of
  Circle r -> r * r
  Square w h -> w * h

-- Literals chosen by a case meet a case on them.
digit :: Int -> String
digit n = case (case n of
    0 -> 10
    1 -> 20
    _ -> 30) of
  10 -> "zero"
  20 -> "one"
  _ -> "many"

-- Alternatives that several chosen values reach are copied only while small.
classify :: Int -> String
classify n = case (if n > 10 then Just n else if n > 5 then Just (n * 2) else Nothing) of
  Just m -> show m <> show m <> show m <> show m <> show m <> show m <> show m <> show m <> show m <> show m <> show m
  Nothing -> "none"

large :: Int -> String
large n = case (if n > 10 then Just n else if n > 5 then Just (n * 2) else Nothing) of
  Just m -> show m <> show m <> show m <> show m <> show m <> show m <> show m <> show m <> show m <> show m <> show m <> show m <> show m <> show m <> show m <> show m <> show m <> show m <> show m <> show m
  Nothing -> "none"

main :: Array String
main =
  [ firstId [ { id: "a" } ]
  , show (second [ 1, 2 ])
  , show (measure 3)
  , digit (opaque 1)
  , classify (opaque 11)
  , large (opaque 12)
  ]
