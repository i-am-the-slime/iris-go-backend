module Fun.CallerMaps where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..), fst, snd)
import Data.Tuple.Nested (type (/\), (/\))
import Effect (Effect)
import Effect.Console (log)

main :: Effect Unit
main = do
  log "-- a loop hands its map to a function that a shared map is handed to as well"
  let counted = foldl (\table chunk -> countAll chunk 0 table) Map.empty (chunks 12)
  log (show (Map.toUnfoldable counted :: Array (Int /\ Int)))
  log "-- the shared map, handed on twice, is seen as it was by both"
  let base = countAll [ 1, 2, 3 ] 0 Map.empty
  let more = countAll [ 1, 1 ] 0 base
  let other = countAll [ 3, 4 ] 0 base
  log (show (Map.toUnfoldable more :: Array (Int /\ Int)))
  log (show (Map.toUnfoldable other :: Array (Int /\ Int)))
  log (show (Map.toUnfoldable base :: Array (Int /\ Int)))
  log "-- a function that answers a pair of a count and the record it updated"
  let tally = foldl (\state word -> tallied word state) { tallies: { total: 0, byWord: Map.empty }, repeats: 0 } (words 40)
  log (show tally.repeats <> " " <> show tally.tallies.total <> " " <> show (Map.size tally.tallies.byWord))
  log "-- the record handed to it twice: both answers start from the same record"
  let start = snd (bumpAll [ "a", "b", "a" ] 0 0 { total: 0, byWord: Map.empty })
  let Tuple first afterFirst = bumpAll [ "a", "c" ] 0 0 start
  let Tuple second afterSecond = bumpAll [ "b", "b" ] 0 0 start
  log (show first <> " " <> show (Map.toUnfoldable afterFirst.byWord :: Array (String /\ Int)))
  log (show second <> " " <> show (Map.toUnfoldable afterSecond.byWord :: Array (String /\ Int)))
  log (show (Map.toUnfoldable start.byWord :: Array (String /\ Int)))
  log "-- a pair whose record is shown in order"
  let pair = bumpAll [ "z", "y", "z" ] 0 0 { total: 0, byWord: Map.empty }
  log (show (fst pair) <> " " <> show (Map.keys (snd pair).byWord))

chunks :: Int -> Array (Array Int)
chunks count = Array.range 1 count <#> \n -> Array.range n (n + n `mod` 4) <#> \k -> (k * 7) `mod` 10

words :: Int -> Array String
words count = Array.range 1 count <#> \n -> show ((n * 5) `mod` 9)

-- | Counts the numbers from a position on, one at a time.
countAll :: Array Int -> Int -> Map Int Int -> Map Int Int
countAll numbers position table = case Array.index numbers position of
  Nothing -> table
  Just number -> countAll numbers (position + 1) (Map.insertWith (+) number 1 table)

type Tallies = { total :: Int, byWord :: Map String Int }

tallied :: String -> { tallies :: Tallies, repeats :: Int } -> { tallies :: Tallies, repeats :: Int }
tallied word state = do
  let Tuple before tallies = bumpAll [ word ] 0 0 state.tallies
  { tallies, repeats: state.repeats + before }

-- | Counts the words from a position on, answering how often they were seen before.
bumpAll :: Array String -> Int -> Int -> Tallies -> Int /\ Tallies
bumpAll words position seen tallies = case Array.index words position of
  Nothing -> seen /\ tallies
  Just word -> do
    let before = case Map.lookup word tallies.byWord of
          Nothing -> 0
          Just times -> times
    bumpAll words (position + 1) (seen + before) tallies { total = tallies.total + 1, byWord = Map.insert word (before + 1) tallies.byWord }
