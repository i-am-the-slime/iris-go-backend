module Main where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Map as Map
import Data.Tuple.Nested (type (/\), (/\))
import Effect (Effect)
import Effect.Console (log)

data Descending = Descending Int Int

derive instance Eq Descending

instance Ord Descending where
  compare (Descending a b) (Descending c d) = compare (c /\ d) (a /\ b)

instance Show Descending where
  show (Descending a b) = "Descending " <> show a <> " " <> show b

newtype Swapped = Swapped (Int /\ Int)

derive instance Eq Swapped

instance Ord Swapped where
  compare (Swapped (a /\ b)) (Swapped (c /\ d)) = compare (b /\ a) (d /\ c)

instance Show Swapped where
  show (Swapped cell) = "Swapped " <> show cell

main :: Effect Unit
main = do
  log (show (Map.toUnfoldable (descending 8) :: Array _))
  log (show (Map.toUnfoldable (swapped 8) :: Array _))
  log (show (Map.toUnfoldable (measured 8) :: Array _))
  where
  descending n = foldl (\m k -> Map.insert (Descending (k `mod` 3) k) k m) Map.empty (Array.range 1 n)
  swapped n = foldl (\m k -> Map.insert (Swapped (k `mod` 3 /\ k)) k m) Map.empty (Array.range 1 n)
  measured n = foldl (\m k -> Map.insert ((if k == 3 then 0.0 else -0.0) /\ k `mod` 2) k m) Map.empty (Array.range 1 n)
