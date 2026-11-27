module Fun.LeastKeys where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Data.String.CodeUnits as CodeUnits
import Data.Tuple.Nested (type (/\), (/\))
import Effect (Effect)
import Effect.Console (log)

main :: Effect Unit
main = do
  log "-- a queue of tasks by priority, drained one least key at a time, refilled on the way"
  log (show (drainedByPriority 60))
  log "-- the greatest key, taken off while new ones go in"
  log (show (takenFromTheTop 40))
  log "-- shortest distances, a map of the nodes to visit by distance as the queue"
  log (show (shortestDistances 30))
  log "-- a set's least element, taken while the set grows and shrinks"
  log (show (smallestFirst [ 9, 3, 7, 1, 8, 2, 6, 4, 5, 0 ]))
  log "-- the least key of a map that a function only reads"
  log (show (leastAfterEach (Array.range 1 25 <#> \n -> (n * 13) `mod` 29)))
  log "-- the least and greatest keys of an empty map, and of one emptied again"
  log (show (Map.findMin (emptied 5)) <> " " <> show (Map.findMax (emptied 5)))
  log "-- Char keys, least first"
  log (show (lettersInOrder "ordered maps keep their keys in order"))

-- | Takes the task of the least priority, and every third one puts two new ones in.
drainedByPriority :: Int -> Array Int
drainedByPriority count = (go 0 [] (Map.fromFoldable (Array.range 1 count <#> \n -> ((n * 37) `mod` 101) /\ n))).done
  where
  go step done queue = case Map.findMin queue of
    Nothing -> { done, queue }
    Just { key, value }
      | step `mod` 3 == 0 && step < 40 -> go (step + 1) (Array.snoc done value) (Map.insert (key + 50) (value * 10) (Map.insert (key + 7) (value + 1000) (Map.delete key queue)))
      | otherwise -> go (step + 1) (Array.snoc done value) (Map.delete key queue)

takenFromTheTop :: Int -> Array Int
takenFromTheTop count = (foldl step { taken: [], heap: Map.empty } (Array.range 1 count)).taken
  where
  step { taken, heap } n = do
    let grown = Map.insert ((n * 17) `mod` 23) n heap
    if n `mod` 2 == 0 then case Map.findMax grown of
      Nothing -> { taken, heap: grown }
      Just { key, value } -> { taken: Array.snoc taken (key * 100 + value), heap: Map.delete key grown }
    else { taken, heap: grown }

-- | Dijkstra on a ring with chords, the queue a map of distance and node to nothing.
shortestDistances :: Int -> Array (Int /\ Int)
shortestDistances size = Map.toUnfoldable (go (Map.singleton (0 /\ 0) unit) Map.empty)
  where
  go :: Map (Int /\ Int) Unit -> Map Int Int -> Map Int Int
  go queue settled = case Map.findMin queue of
    Nothing -> settled
    Just { key: distance /\ node }
      | Map.member node settled -> go (Map.delete (distance /\ node) queue) settled
      | otherwise -> go (foldl (\q (next /\ weight) -> Map.insert ((distance + weight) /\ next) unit q) (Map.delete (distance /\ node) queue) (edges node)) (Map.insert node distance settled)
  edges node = [ ((node + 1) `mod` size) /\ 3, ((node * 7 + 2) `mod` size) /\ 5, ((node + size - 1) `mod` size) /\ 4 ]

smallestFirst :: Array Int -> Array Int
smallestFirst = _.taken <<< foldl step { taken: [], set: Set.empty :: Set Int }
  where
  step { taken, set } n = do
    let grown = Set.insert n (Set.insert (n + 20) set)
    case Set.findMin grown of
      Just least | n `mod` 2 == 1 -> { taken: Array.snoc taken least, set: Set.delete least grown }
      _ -> { taken, set: grown }

leastAfterEach :: Array Int -> Array Int
leastAfterEach keys = (foldl step { seen: [], map: Map.empty } keys).seen
  where
  step { seen, map } key = do
    let grown = Map.insert key (key * 2) map
    { seen: Array.snoc seen (least grown), map: if key `mod` 4 == 0 then Map.delete (least grown) grown else grown }

least :: Map Int Int -> Int
least map = case Map.findMin map of
  Nothing -> -1
  Just { key } -> key

emptied :: Int -> Map Int Int
emptied count = foldl (\map n -> Map.delete n map) (foldl (\map n -> Map.insert n n map) Map.empty (Array.range 1 count)) (Array.range 1 count)

lettersInOrder :: String -> Array Char
lettersInOrder text = go [] (foldl (\map letter -> Map.insert letter unit map) Map.empty (CodeUnits.toCharArray text))
  where
  go taken map = case Map.findMin map of
    Nothing -> taken
    Just { key } -> go (Array.snoc taken key) (Map.delete key map)
