module Fun.SharedOrdered where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested (type (/\), (/\))
import Effect (Effect)
import Effect.Console (log)

main :: Effect Unit
main = do
  log "-- a version asked for its least key after a later version deleted it"
  log (show (leastBeforeAndAfter 10))
  log "-- every version of a fold kept, each asked for its greatest key at the end"
  log (show (everyVersion 8 <#> Map.findMax))
  log "-- two branches grown from one map"
  log (show (branches 6))
  log "-- a map that a closure keeps, asked for its least key after the next version is made"
  log (show (keptByClosure 5))
  log "-- the same map as two fields of a record, each changed on its own"
  log (show (twoFields 6))
  log "-- an ordered map in a pair whose version is read twice"
  log (show (pairReadTwice 7))
  log "-- a map a fold owns, shared once the fold is done"
  log (show (ownedThenShared 12))
  log (show (Map.findMax (queueOf 20)))

leastBeforeAndAfter :: Int -> Array (Maybe Int)
leastBeforeAndAfter count = do
  let map = foldl (\m n -> Map.insert ((n * 7) `mod` 11) n m) Map.empty (Array.range 1 count)
  let without = case Map.findMin map of
        Just { key } -> Map.delete key map
        Nothing -> map
  [ _.key <$> Map.findMin map, _.key <$> Map.findMin without, _.key <$> Map.lookupGT 3 map, _.key <$> Map.lookupLE 3 without ]

everyVersion :: Int -> Array (Map Int Int)
everyVersion count = Array.scanl (\map n -> case Map.findMin map of
    Just { key } | n `mod` 3 == 0 -> Map.insert (n * 2) n (Map.delete key map)
    _ -> Map.insert (n * 2) n map) Map.empty (Array.range 1 count)

branches :: Int -> String
branches count = do
  let trunk = foldl (\map n -> Map.insert n (n * n) map) Map.empty (Array.range 1 count)
  let left = Map.delete 1 trunk
  let right = Map.insert 0 0 trunk
  show (Map.findMin left) <> show (Map.findMin right) <> show (Map.findMin trunk) <> show (Map.lookupGE 1 left)

keptByClosure :: Int -> String
keptByClosure count = do
  let map = foldl (\m n -> Map.insert n n m) Map.empty (Array.range 1 count)
  let ask = \_ -> Map.findMin map
  let next = Map.delete 1 map
  show (ask unit) <> show (Map.findMin next)

twoFields :: Int -> String
twoFields count = do
  let map = foldl (\m n -> Map.insert n n m) Map.empty (Array.range 1 count)
  let record = { early: Map.delete count map, late: Map.delete 1 map }
  show (Map.findMax record.early) <> show (Map.findMin record.late)

pairReadTwice :: Int -> String
pairReadTwice count = do
  let built = foldl (\(m /\ total) n -> Map.insert n n m /\ (total + n)) (Map.empty /\ 0) (Array.range 1 count)
  let first /\ total = built
  let second /\ _ = built
  show (Map.findMin (Map.delete 1 first)) <> show (Map.findMin second) <> show total

ownedThenShared :: Int -> String
ownedThenShared count = do
  let map = queueOf count
  let without = Map.delete 10 map
  show (Map.findMin map) <> show (Map.lookupLE 10 without) <> show (Map.lookupLE 10 map)

queueOf :: Int -> Map Int Int
queueOf count = foldl step Map.empty (Array.range 1 count)
  where
  step m n = case Map.findMin m of
    Just { key } | Map.size m > 3 -> Map.insert n n (Map.delete key m)
    _ -> Map.insert n n m
