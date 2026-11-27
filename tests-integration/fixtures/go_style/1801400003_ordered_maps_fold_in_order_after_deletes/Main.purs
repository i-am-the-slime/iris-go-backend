module Fun.OrderedFolds where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl, foldr, sum)
import Data.FoldableWithIndex (foldlWithIndex, foldrWithIndex)
import Data.List as List
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.Tuple.Nested (type (/\), (/\))
import Effect (Effect)
import Effect.Console (log)

main :: Effect Unit
main = do
  let thinned = evicted 80
  log "-- a map that evicts its least keys as it grows, then walked in order"
  log (show (Map.toUnfoldable thinned :: Array (Int /\ Int)))
  log (show (Map.keys thinned))
  log (show (Map.values thinned))
  log (show (foldl (\text value -> text <> show value <> ";") "" thinned))
  log (show (foldr (\value text -> show value <> ";" <> text) "" thinned))
  log (show (foldlWithIndex (\key text value -> text <> show key <> "=" <> show value <> " ") "" thinned))
  log (show (foldrWithIndex (\key value text -> show key <> ":" <> show value <> " " <> text) "" thinned))
  log (show (sum thinned) <> " " <> show (Map.size thinned))
  log "-- walked in order between writes, so that each walk sees the map as it was then"
  log (show (walkedBetweenWrites 12))
  log "-- the entries of a map emptied by its least keys, as an array"
  log (show (Map.toUnfoldable (drained 10) :: Array (Int /\ String)))
  log "-- a set thinned by its greatest elements, as an array and a list"
  log (show (Set.toUnfoldable (thinnedSet 30) :: Array Int))
  log (show (Set.toUnfoldable (thinnedSet 30) :: List.List Int))
  log "-- the difference of two maps that ask for their least keys"
  log (show (Map.toUnfoldable (differenceOfQueues 25) :: Array (Int /\ Int)))

-- | Inserts keys in a shuffled order and evicts the least one whenever there are more than 20.
evicted :: Int -> Map Int Int
evicted count = foldl step Map.empty (Array.range 1 count)
  where
  step map n = do
    let grown = Map.insert ((n * 29) `mod` 97) n map
    if Map.size grown > 20 then case Map.findMin grown of
      Nothing -> grown
      Just { key } -> Map.delete key grown
    else grown

walkedBetweenWrites :: Int -> Array String
walkedBetweenWrites count = (foldl step { walks: [], map: Map.empty } (Array.range 1 count)).walks
  where
  step { walks, map } n = do
    let grown = Map.insert ((n * 5) `mod` 13) n map
    let thinned = case Map.findMax grown of
          Just { key } | n `mod` 4 == 0 -> Map.delete key grown
          _ -> grown
    { walks: Array.snoc walks (show (Map.keys thinned)), map: thinned }

drained :: Int -> Map Int String
drained count = go 0 (foldl (\map n -> Map.insert ((n * 3) `mod` 17) (show n) map) Map.empty (Array.range 1 count))
  where
  go taken map
    | taken >= count / 2 = map
    | otherwise = case Map.findMin map of
        Nothing -> map
        Just { key } -> go (taken + 1) (Map.delete key map)

thinnedSet :: Int -> Set.Set Int
thinnedSet count = foldl step Set.empty (Array.range 1 count)
  where
  step set n = do
    let grown = Set.insert ((n * 7) `mod` 41) set
    if n `mod` 5 == 0 then case Set.findMax grown of
      Just greatest -> Set.delete greatest grown
      Nothing -> grown
    else grown

differenceOfQueues :: Int -> Map Int Int
differenceOfQueues count = do
  let queue = evicted count
  let others = foldl (\map n -> Map.insert (n * 4) n map) Map.empty (Array.range 1 count)
  let without = case Map.findMin others of
        Just { key } -> Map.delete key others
        Nothing -> others
  Map.difference queue without
