module Main where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Tuple.Nested (type (/\), (/\))
import Effect (Effect)
import Effect.Console (logShow)

type Cache = { capacity :: Int, clock :: Int, entries :: Map Int Int, keysByLastUse :: Map Int Int }

data Operation = Get Int | Put Int Int

main :: Effect Unit
main = do
  let finished = operations # foldl perform { cache: emptyCache 3, seen: [] }
  logShow finished.seen
  logShow (Map.toUnfoldable finished.cache.entries :: Array (Int /\ Int))
  logShow (Map.toUnfoldable finished.cache.keysByLastUse :: Array (Int /\ Int))
  where
  operations = Array.range 1 30 <#> \n -> if n `mod` 3 == 0 then Get (n `mod` 4) else Put (n `mod` 5) n
  perform { cache, seen } = case _ of
    Get key -> do
      let found /\ touched = get key cache
      { cache: touched, seen: Array.snoc seen (fromMaybe (-1) found) }
    Put key value -> { cache: put key value cache, seen }

emptyCache :: Int -> Cache
emptyCache capacity = { capacity, clock: 0, entries: Map.empty, keysByLastUse: Map.empty }

get :: Int -> Cache -> Maybe Int /\ Cache
get key cache = case Map.lookup key cache.entries of
  Nothing -> Nothing /\ cache
  Just value -> Just value /\ remember key value (forget key cache)

put :: Int -> Int -> Cache -> Cache
put key value cache
  | Map.member key cache.entries = remember key value (forget key cache)
  | Map.size cache.entries < cache.capacity = remember key value cache
  | otherwise = remember key value (evict cache)

remember :: Int -> Int -> Cache -> Cache
remember key value cache = cache
  { clock = cache.clock + 1
  , entries = Map.insert key value cache.entries
  , keysByLastUse = Map.insert cache.clock key cache.keysByLastUse
  }

forget :: Int -> Cache -> Cache
forget key cache = cache { keysByLastUse = Map.filter (_ /= key) cache.keysByLastUse }

evict :: Cache -> Cache
evict cache = case Map.findMin cache.keysByLastUse of
  Nothing -> cache
  Just { key: lastUsed, value: key } -> cache { entries = Map.delete key cache.entries, keysByLastUse = Map.delete lastUsed cache.keysByLastUse }
