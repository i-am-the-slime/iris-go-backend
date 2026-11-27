module Fun.RecordMaps where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Set (Set)
import Data.Set as Set
import Data.Tuple.Nested (type (/\))
import Effect (Effect)
import Effect.Console (log)

main :: Effect Unit
main = do
  log "-- a window that slides along the letters, remembering where it saw each"
  log (show (longestUniqueStretch [ 'a', 'b', 'c', 'a', 'b', 'c', 'b', 'b' ]))
  log (show (longestUniqueStretch [ 'p', 'w', 'w', 'k', 'e', 'w' ]))
  log "-- a record taken apart in the fold's step, its map updated"
  log (show (sizesWhileInserting (Array.range 1 25 <#> \n -> n * 7 `mod` 11)))
  log "-- a record in a record"
  log (tallyReport 40)
  log (tallyReport 7)
  log "-- a record handed to a function that looks a field up and updates it"
  log (visitReport 30)
  log (visitReport 5)
  log "-- a record whose map is read in order once it is built"
  log (show (Map.keys (indexed (digits 20 <#> show)).positions))
  log (show (Map.keys (Map.insert "first" 0 (indexed (digits 4 <#> show)).positions)))

-- | The digits of the multiples of seven, as many as asked for.
digits :: Int -> Array Int
digits count = Array.range 1 count <#> \n -> (n * 7) `mod` 10 + n `div` 9

type Window = { start :: Int, longest :: Int, lastSeen :: Map Char Int }

longestUniqueStretch :: Array Char -> Int
longestUniqueStretch letters = (Array.foldl slide { start: 0, longest: 0, lastSeen: Map.empty } (Array.mapWithIndex (\i c -> { position: i, letter: c }) letters)).longest
  where
  slide window { position, letter } = do
    let
      start = case Map.lookup letter window.lastSeen of
        Just seen | seen >= window.start -> seen + 1
        _ -> window.start
    { start, longest: max window.longest (position - start + 1), lastSeen: Map.insert letter position window.lastSeen }

sizesWhileInserting :: Array Int -> Array Int
sizesWhileInserting all = (foldl step { table: Map.empty, sizes: [] } all).sizes
  where
  step { table, sizes } key = do
    let grown = Map.insert key unit table
    { table: grown, sizes: if key `mod` 3 == 0 then Array.snoc sizes (Map.size grown) else sizes }

tallyReport :: Int -> String
tallyReport count = do
  let tallied = tally (digits count)
  show tallied.counts.total <> " " <> show (Map.toUnfoldable tallied.counts.byValue :: Array (Int /\ Int))

type Counts = { total :: Int, byValue :: Map Int Int }

tally :: Array Int -> { counts :: Counts, last :: Int }
tally = foldl (\state value -> state { counts = state.counts { total = state.counts.total + 1, byValue = Map.insertWith (+) value 1 state.counts.byValue }, last = value }) { counts: { total: 0, byValue: Map.empty }, last: 0 }

type Visits = { visited :: Set Int, repeats :: Int }

visitReport :: Int -> String
visitReport count = do
  let visits = foldl (\visited node -> visit visited node) { visited: Set.empty, repeats: 0 } (digits count)
  show (Set.toUnfoldable visits.visited :: Array Int) <> " " <> show visits.repeats

visit :: Visits -> Int -> Visits
visit visits node
  | Set.member node visits.visited = visits { repeats = visits.repeats + 1 }
  | otherwise = visits { visited = Set.insert node visits.visited }

indexed :: Array String -> { positions :: Map String Int, count :: Int }
indexed = foldl (\state word -> { positions: Map.alter (Just <<< fromMaybe state.count) word state.positions, count: state.count + 1 }) { positions: Map.empty, count: 0 }
