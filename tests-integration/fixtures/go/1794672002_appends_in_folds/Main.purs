module Main where

import Prelude

import Data.Array ((..))
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldl)

appendSingletons :: Array Int -> Array Int
appendSingletons = foldl (\acc x -> acc <> [ x ]) []

snocs :: Array Int -> Array Int
snocs = foldl (\acc x -> Array.snoc acc (x * 2)) [ 1 ]

-- The array grows inside `Right`, as yoga-json's `sequenceCombining` builds it.
combining :: Array (Either String Int) -> Either String (Array Int)
combining = foldl step (Right [])
  where
  step acc element = case acc, element of
    Left errors, Left more -> Left (errors <> more)
    Left errors, Right _ -> Left errors
    Right values, Right value -> Right (values <> pure value)
    Right _, Left errors -> Left errors

-- `seen` keeps every earlier `acc`, so `acc` is copied, not appended to in place.
escaping :: Array Int -> Array (Array Int)
escaping xs = (foldl (\r x -> { acc: r.acc <> [ x ], seen: r.seen <> [ r.acc ] }) { acc: [], seen: [] } xs).seen

main :: { appended :: Array Int, snocs :: Array Int, combined :: Either String (Array Int), escaping :: Array (Array Int) }
main =
  { appended: appendSingletons (1 .. 5)
  , snocs: snocs (1 .. 5)
  , combined: combining [ Right 1, Right 2, Right 3 ]
  , escaping: escaping (1 .. 4)
  }
