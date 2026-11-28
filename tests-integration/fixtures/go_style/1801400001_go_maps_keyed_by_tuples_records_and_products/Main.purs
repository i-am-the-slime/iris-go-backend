module Main where

import Prelude

import Data.Array as Array
import Data.Char (fromCharCode)
import Data.Foldable (foldl, foldr)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Set as Set
import Data.Tuple.Nested (type (/\), (/\))
import Effect (Effect)
import Effect.Console (log)

newtype Cell = Cell (Int /\ Int)

derive newtype instance Eq Cell
derive newtype instance Ord Cell

instance Show Cell where
  show (Cell cell) = "Cell " <> show cell

data Point = Point Int String

derive instance Eq Point
derive instance Ord Point

instance Show Point where
  show (Point x label) = "Point " <> show x <> " " <> show label

main :: Effect Unit
main = do
  log "-- Tuple keys"
  log (show (Map.toUnfoldable (grid 6) :: Array _))
  log (show (foldr Array.cons [] (grid 4)))
  log "-- nested tuples"
  log (show (Map.toUnfoldable (nested 30) :: Array _))
  log "-- record keys, labels in order"
  log (show (Map.toUnfoldable (records [ "b", "a", "\xE000", "\x1F600", "a\xFFFF", "a\x10000", "" ]) :: Array _))
  log "-- newtype and data keys"
  log (show (Map.toUnfoldable (cells 12) :: Array _))
  log (show (Map.toUnfoldable (points [ "z", "\x1F600", "\xE001", "y" ]) :: Array _))
  log "-- many keys sort field by field: negative and extreme Ints, Chars"
  log (show (Map.toUnfoldable (spread 90) :: Array _))
  log (show (Map.keys (lettered 60)))
  log "-- sets of tuples"
  log (show (Set.toUnfoldable (visited 40) :: Array _))
  where
  grid n = foldl (\m k -> Map.insert (k `mod` n /\ (n - k `mod` 3)) k m) Map.empty (Array.range 1 (n * 5))
  nested n = foldl (\m k -> Map.insertWith (+) ((k `mod` 3 /\ k `mod` 2) /\ ("w" <> show (k `mod` 4))) k m) Map.empty (Array.range 1 n)
  records words = foldl (\m (index /\ word) -> Map.insert { word, index: index `mod` 2, length: 3 - index `mod` 3 } index m) Map.empty (Array.mapWithIndex (/\) words)
  cells n = foldl (\m k -> Map.insert (Cell ((k * 7) `mod` 5 /\ -k)) k m) Map.empty (Array.range 1 n)
  points words = foldl (\m (index /\ word) -> Map.insert (Point (index `mod` 2) word) index m) Map.empty (Array.mapWithIndex (/\) words)
  spread n = foldl (\m k -> Map.insert (((k `mod` 3) - 1) * 2147483647 /\ (((k * 48271) `mod` 65537) - 32768)) k m) Map.empty (Array.range 1 n)
  lettered n = foldl (\m k -> Map.insert { letter: fromMaybe 'a' (fromCharCode (32 + ((k * 37) `mod` 300))), row: negate (k `mod` 3) } k m) Map.empty (Array.range 1 n)
  visited n = foldl (\s k -> Set.insert ((k * 13) `mod` 7 /\ k `mod` 4) s) Set.empty (Array.range 1 n)
