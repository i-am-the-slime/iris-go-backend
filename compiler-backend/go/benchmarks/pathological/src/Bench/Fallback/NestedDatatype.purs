module Bench.Fallback.NestedDatatype where

import Prelude

import Bench.Harness (benchmark)
import Data.Array ((..))
import Data.Foldable (foldl)
import Data.Tuple.Nested (type (/\), (/\))
import Effect (Effect)

hypothesis :: String
hypothesis = "a binary random-access list is a nested datatype; its functions recurse polymorphically, so Go erases elements to any and asserts at every level"

data Sequence a
  = Empty
  | Zero (Sequence (a /\ a))
  | One a (Sequence (a /\ a))

main :: Effect Unit
main = benchmark { size: 300000, workload }

workload :: Int -> String
workload n = do
  let sequence = foldl (flip cons) Empty (1 .. n)
  show (size sequence) <> " " <> show (total identity sequence) <> " " <> show (total identity (mapSequence (_ * 3) sequence))

cons :: forall a. a -> Sequence a -> Sequence a
cons x = case _ of
  Empty -> One x Empty
  Zero rest -> One x rest
  One y rest -> Zero (cons (x /\ y) rest)

size :: forall a. Sequence a -> Int
size = case _ of
  Empty -> 0
  Zero rest -> 2 * size rest
  One _ rest -> 1 + 2 * size rest

total :: forall a. (a -> Int) -> Sequence a -> Int
total measure = case _ of
  Empty -> 0
  Zero rest -> total pair rest
  One x rest -> measure x + total pair rest
  where
  pair (left /\ right) = (measure left + measure right) `mod` 1000003

mapSequence :: forall a b. (a -> b) -> Sequence a -> Sequence b
mapSequence f = case _ of
  Empty -> Empty
  Zero rest -> Zero (mapSequence (\(left /\ right) -> f left /\ f right) rest)
  One x rest -> One (f x) (mapSequence (\(left /\ right) -> f left /\ f right) rest)
