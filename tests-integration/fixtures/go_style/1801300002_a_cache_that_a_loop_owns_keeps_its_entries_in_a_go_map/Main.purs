module Fun.LeastRecentlyUsed where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Tuple.Nested (type (/\), (/\))
import Effect (Effect)
import Effect.Console (log)

main :: Effect Unit
main = do
  log "-- a cache that a loop owns, whose lookups answer it in a pair"
  log (performed 16 (Array.range 1 300 <#> \n -> if n `mod` 3 == 0 then Get ((n * 7) `mod` 40) else Put ((n * 11) `mod` 40) n))
  log (performed 2 [ Put 1 1, Put 2 2, Get 1, Put 3 3, Get 2, Put 4 4, Get 1, Get 3, Get 4 ])
  log "-- one cache looked up three times: each lookup starts from the same cache"
  log (lookedUpThrice (put 4 4 (put 3 3 (put 2 2 (put 1 1 (emptyCache 3))))))
  log (lookedUpThrice (put 5 5 (put 2 2 (emptyCache 3))))

performed :: Int -> Array Operation -> String
performed capacity operations = do
  let done = foldl perform { cache: emptyCache capacity, checksum: 0 } operations
  show done.checksum <> " " <> show (Map.keys done.cache.entries)
  where
  perform { cache, checksum } = case _ of
    Get key -> do
      let found /\ touched = get key cache
      { cache: touched, checksum: (checksum * 31 + fromMaybe (-1) found + 1) `mod` 1000003 }
    Put key value -> { cache: put key value cache, checksum }

lookedUpThrice :: Cache -> String
lookedUpThrice cache = do
  let two /\ afterTwo = get 2 cache
  let three /\ afterThree = get 3 cache
  let five /\ afterFive = get 5 cache
  show [ two, three, five ]
    <> " " <> show (Map.toUnfoldable (put 9 9 afterTwo).entries :: Array (Int /\ Entry))
    <> " " <> show (Map.toUnfoldable afterThree.entries :: Array (Int /\ Entry))
    <> " " <> show (Map.keys afterFive.keysByLastUse)
    <> " " <> show (Map.toUnfoldable (put 9 9 cache).entries :: Array (Int /\ Entry))

data Operation = Get Int | Put Int Int

type Cache = { capacity :: Int, clock :: Int, entries :: Map Int Entry, keysByLastUse :: Map Int Int }

type Entry = { value :: Int, lastUsed :: Int }

emptyCache :: Int -> Cache
emptyCache capacity = { capacity, clock: 0, entries: Map.empty, keysByLastUse: Map.empty }

get :: Int -> Cache -> Maybe Int /\ Cache
get key cache = case Map.lookup key cache.entries of
  Nothing -> Nothing /\ cache
  Just entry -> Just entry.value /\ remember key entry.value (forgetUse entry cache)

put :: Int -> Int -> Cache -> Cache
put key value cache = case Map.lookup key cache.entries of
  Just entry -> remember key value (forgetUse entry cache)
  Nothing
    | Map.size cache.entries < cache.capacity -> remember key value cache
    | otherwise -> remember key value (evictLeastRecentlyUsed cache)

remember :: Int -> Int -> Cache -> Cache
remember key value cache = cache
  { clock = cache.clock + 1
  , entries = Map.insert key { value, lastUsed: cache.clock } cache.entries
  , keysByLastUse = Map.insert cache.clock key cache.keysByLastUse
  }

forgetUse :: Entry -> Cache -> Cache
forgetUse { lastUsed } cache = cache { keysByLastUse = Map.delete lastUsed cache.keysByLastUse }

evictLeastRecentlyUsed :: Cache -> Cache
evictLeastRecentlyUsed cache = case Map.findMin cache.keysByLastUse of
  Nothing -> cache
  Just { key: lastUsed, value: key } -> cache { entries = Map.delete key cache.entries, keysByLastUse = Map.delete lastUsed cache.keysByLastUse }
