module Main where

import Prelude

import Data.Foldable (foldl)
import Data.FoldableWithIndex (foldlWithIndex)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Data.Tuple.Nested (type (/\), (/\))
import Effect (Effect)
import Effect.Console (log)

foreign import timed :: forall a. (Unit -> a) -> Effect a

main :: Effect Unit
main = do
  log "-- maps built from empty in a timed callback come back in order"
  ints <- timed \_ -> foldl (\built key -> Map.insert key key built) Map.empty keys
  log (show (Map.toUnfoldable ints :: Array (Int /\ Int)))
  log (show (keysInOrder ints))
  pairs <- timed \_ -> foldl (\built key -> Map.insert (key `mod` 3 /\ key / 3) key built) Map.empty keys
  log (show (Map.toUnfoldable pairs :: Array ((Int /\ Int) /\ Int)))
  words <- timed \_ -> foldl (\built word -> Map.insert word 1 built) Map.empty names
  log (show (Map.toUnfoldable words :: Array (String /\ Int)))
  counted <- timed \_ -> foldl (\counts key -> Map.alter increment (key `mod` 4) counts) Map.empty keys
  log (show (Map.toUnfoldable counted :: Array (Int /\ Int)))
  summed <- timed \_ -> foldl (\counts key -> Map.insertWith (+) (key `mod` 4) key counts) Map.empty keys
  log (show (keysInOrder summed) <> " " <> show (foldl (\seen value -> seen <> [ value ]) [] summed))
  log "-- sets built from empty in a timed callback come back in order"
  intSet <- timed \_ -> foldl (flip Set.insert) Set.empty keys
  log (show (Set.toUnfoldable intSet :: Array Int))
  log (show (foldl (\checksum key -> (checksum * 31 + key) `mod` 1000003) 0 intSet))
  wordSet <- timed \_ -> foldl (flip Set.insert) Set.empty names
  log (show (Set.toUnfoldable wordSet :: Array String))
  log (show (foldl (\joined word -> joined <> word) "" (wordSet :: Set String)))
  log "-- a map a timed callback builds is not changed by an insert into it or an effect run twice"
  table <- timed \_ -> foldl (\built key -> Map.insert key key built) Map.empty keys
  let bigger = Map.insert 99 99 table
  log (show (Map.size bigger))
  log (show (Map.member 99 table))
  let bump = log (show (Map.lookup 3 (Map.insertWith (+) 3 100 table)))
  bump
  bump
  log (show (Map.lookup 3 table) <> " " <> show (Map.size table))
  where
  keys = [ 17, 3, 11, 3, 29, 0, 8, 17, 22, 5, 14 ]
  names = [ "pear", "apple", "fig", "apple", "kiwi", "banana", "fig" ]

keysInOrder :: Map Int Int -> Array Int
keysInOrder = foldlWithIndex (\key seen _ -> seen <> [ key ]) []

increment :: Maybe Int -> Maybe Int
increment (Just count) = Just (count + 1)
increment Nothing = Just 1
