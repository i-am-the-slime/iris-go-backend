module Main where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Tuple.Nested (type (/\), (/\))
import Effect (Effect)
import Effect.Console (log)

-- | Answers its argument.
foreign import handedOver :: forall a. a -> Effect a

-- | Calls the callback twice and answers what it answered the second time.
foreign import twice :: forall a. (Unit -> a) -> Effect a

main :: Effect Unit
main = do
  log "-- a map handed through a foreign is looked up by a callback the foreign runs twice"
  table <- handedOver (squares (Array.range 1 20))
  found <- twice \_ -> foldl (\total key -> total + fromMaybe 0 (Map.lookup key table)) 0 (Array.range 0 25)
  log (show found)
  log "-- a callback that counts into a map it closes over starts from a copy each time"
  bumped <- twice \_ -> foldl (\counts key -> Map.insertWith (+) key 1 counts) table (Array.range 0 2 <#> \n -> n `div` 2 + 1)
  log (show (Map.lookup 1 bumped) <> " " <> show (Map.lookup 2 bumped) <> " " <> show (Map.lookup 1 table))
  trimmed <- twice \_ -> foldl (\kept key -> Map.delete key kept) table (Array.filter (\key -> key < 4 || key == 5) (Array.range 1 6))
  log (show (Map.toUnfoldable trimmed :: Array (Int /\ Int)))
  log (show (Map.size table))
  log "-- a map a callback builds comes back in order"
  built <- twice \_ -> foldl (\counts key -> Map.insertWith (+) (key `mod` 5) 1 counts) Map.empty (Array.range 1 23)
  log (show (Map.toUnfoldable built :: Array (Int /\ Int)))
  log "-- a function that reads a map an insert changes afterwards reads the map it closed over"
  let before = Map.fromFoldable [ 1 /\ 10, 2 /\ 20 ]
  let peek key = Map.lookup key before
  let after = Map.insert 3 30 before
  log (show (peek 3) <> " " <> show (Map.lookup 3 after) <> " " <> show (Map.size before))
  log "-- sums count from zero, other combinations from the first value"
  let summed = foldl (\sums key -> Map.insertWith (+) (key `mod` 3) key sums) Map.empty (Array.range 1 7)
  log (show (Map.toUnfoldable summed :: Array (Int /\ Int)))
  let shifted = foldl (\sums key -> Map.insertWith (\old new -> old + new + 100) (key `mod` 3) key sums) Map.empty (Array.range 1 7)
  log (show (Map.toUnfoldable shifted :: Array (Int /\ Int)))

squares :: Array Int -> Map Int Int
squares = foldl (\table key -> Map.insert key (key * key) table) Map.empty
