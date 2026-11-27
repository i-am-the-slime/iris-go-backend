module Main where

import Prelude

import Data.Array as Array
import Data.Char (fromCharCode)
import Data.Foldable (foldl)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import Data.Set as Set
import Data.String.CodeUnits (fromCharArray)
import Data.Tuple.Nested (type (/\), (/\))
import Effect (Effect)
import Effect.Console (log)

main :: Effect Unit
main = do
  log "-- a few Int keys sort by insertion"
  log (show (entries (squares [ 3, -1, 2, 0 ])))
  log "-- many Int keys, negative and spread over the whole range, sort by radix"
  log (show (entries (squares (spread 200))))
  log (show (Set.toUnfoldable (Set.fromFoldable (spread 90 <#> \n -> n * 1000003)) :: Array Int))
  log (show (entries (squares [ top, bottom, 0, -1, 1, top - 1, bottom + 1 ] `Map.union` Map.empty)))
  log (show (Set.toUnfoldable (Set.fromFoldable ([ top, bottom ] <> Array.range (-20) 20)) :: Array Int))
  log "-- values stay with their keys"
  log (show (entries (foldl (\table n -> Map.insert (n * 7919 `mod` 1009) n table) Map.empty (Array.range 1 300))))
  log "-- Char keys"
  log (show (entries (letterCounts (Array.range 0 2000 <#> \n -> letter (n * 37 `mod` 300)))))
  log "-- many String keys: shared prefixes, NUL, lengths around eight bytes"
  log (show (entries (wordIndices (words 120))))
  log (show (Set.toUnfoldable (Set.fromFoldable (prefixed 60)) :: Array String))
  log "-- String keys outside the byte order: private use and astral letters"
  log (show (entries (wordIndices (words 40 <> [ "\xE000", "\x1F600", "a\xFFFF", "a\x10000", "\xD7FF" ]))))
  where
  top = 2147483647
  bottom = -2147483648

entries :: forall k v. Map k v -> Array (k /\ v)
entries = Map.toUnfoldable

squares :: Array Int -> Map Int Int
squares = foldl (\table n -> Map.insert n (n * n) table) Map.empty

spread :: Int -> Array Int
spread count = Array.range 1 count <#> \n -> (n * 48271 `mod` 65537 - 32768) * (if n `mod` 3 == 0 then 65599 else 1)

letter :: Int -> Char
letter code = fromMaybe 'a' (fromCharCode (32 + code))

letterCounts :: Array Char -> Map Char Int
letterCounts = foldl (\counts c -> Map.insertWith (+) c 1 counts) Map.empty

wordIndices :: Array String -> Map String Int
wordIndices = Array.foldl (\table (index /\ word) -> Map.insert word index table) Map.empty <<< Array.mapWithIndex (/\)

words :: Int -> Array String
words count = Array.range 1 count <#> \n -> fromCharArray (Array.range 0 (n `mod` 11) <#> \at -> pick (n * 31 + at * 7))
  where
  pick n = fromMaybe 'a' (fromCharCode (if n `mod` 13 == 0 then 0 else 97 + n `mod` 4))

prefixed :: Int -> Array String
prefixed count = Array.range 1 count <#> \n -> "shared-prefix-" <> show (n * 7 `mod` 61)
