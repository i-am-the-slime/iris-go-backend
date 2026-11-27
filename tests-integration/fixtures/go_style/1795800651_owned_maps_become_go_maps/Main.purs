module Fun.OwnedMaps where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl, foldr, sum)
import Data.FoldableWithIndex (foldlWithIndex)
import Data.List as List
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Set (Set)
import Data.Set as Set
import Data.String.CodeUnits as CodeUnits
import Data.Tuple.Nested (type (/\), (/\))
import Effect (Effect)
import Effect.Console (log)

main :: Effect Unit
main = do
  log "-- inserts, deletes and alters, then the entries in key order"
  log (show (shuffledInsertsAndDeletes 40))
  log (show (Map.toUnfoldable (tally (Array.range 1 30 <#> \n -> (n * 7) `mod` 11)) :: Array (Int /\ Int)))
  log (show (Map.keys (altered 20)))
  log (show (Map.values (updated 20)))
  log "-- folds after updates"
  log (show (sum (squares 25)))
  log (show (foldr (\value text -> show value <> "," <> text) "" (squares 6)))
  log (show (foldlWithIndex (\key total value -> total + key * value) 0 (squares 12)))
  log "-- size, emptiness and lookups on the way"
  log (show (sizesWhileCounting 12))
  log (show (Map.isEmpty (drained 9)))
  log (show (lookups (squares 10) [ 0, 3, 9, 10, -1 ]))
  log "-- singleton, insertWith and fromFoldableWith"
  log (show (Map.insertWith (<>) "a" "!" (Map.singleton "a" "?")))
  log (show (Map.fromFoldableWith (+) (Array.range 1 20 <#> \n -> (n `mod` 4) /\ n)))
  log "-- String keys in JavaScript's order, astral and private-use letters included"
  log (show (wordIndices [ "b", "a", "\xE000", "\x1F600", "ab", "", "B", "a" ]))
  log "-- Char keys"
  log (show (letterCounts "mississippi"))
  log "-- Sets"
  log (show (Set.toUnfoldable (setOfSquares 15) :: Array Int))
  log (show (reachable 6))
  log (show (Set.member 49 (setOfSquares 10)))
  log (show (Set.size (setOfSquares 10)))
  log "-- a map that starts as a tree and is then owned by a fold"
  log (show (withoutEvens (Map.fromFoldable (Array.range 1 12 <#> \n -> n /\ n))))
  log "-- a map that only a reading function sees before it is changed"
  log (show (readThenChange 8))
  log "-- maps that stay trees: kept in a record, captured by a closure, findMin"
  log (show (keptInRecord 5).table)
  log (show (Array.range 0 6 <#> capturedByClosure (squares 6)))
  log (show (smallestFirst (squares 7)))
  log (show (recordKeys 5))

shuffledInsertsAndDeletes :: Int -> Map Int String
shuffledInsertsAndDeletes count = go 0 Map.empty
  where
  go n table
    | n == count = table
    | n `mod` 3 == 2 = go (n + 1) (Map.delete ((n * 17) `mod` count) table)
    | otherwise = go (n + 1) (Map.insert ((n * 17) `mod` count) (show n) table)

tally :: Array Int -> Map Int Int
tally = foldl (\counts n -> Map.insertWith (+) n 1 counts) Map.empty

altered :: Int -> Map Int Int
altered count = foldl step Map.empty (Array.range 1 count)
  where
  step table n = Map.alter (bump n) (n `mod` 7) table
  bump n current = case current of
    Nothing -> Just n
    Just seen | seen > 10 -> Nothing
    Just seen -> Just (seen + n)

updated :: Int -> Map Int Int
updated count = foldl step (squares count) (Array.range 0 count)
  where
  step table n = Map.update (\value -> if value `mod` 2 == 0 then Nothing else Just (value + n)) n table

squares :: Int -> Map Int Int
squares count = foldl (\table n -> Map.insert n (n * n) table) Map.empty (Array.range 0 (count - 1))

sizesWhileCounting :: Int -> Array Int
sizesWhileCounting count = go 0 Map.empty []
  where
  go n table sizes
    | n == count = sizes
    | otherwise = do
        let grown = Map.insert (n `mod` 5) n table
        go (n + 1) grown (Array.snoc sizes (Map.size grown))

drained :: Int -> Map Int Int
drained count = foldl (\table n -> Map.delete n table) (squares count) (Array.range 0 count)

lookups :: Map Int Int -> Array Int -> Array (Maybe Int)
lookups table keys = keys <#> \key -> Map.lookup key table

wordIndices :: Array String -> Map String Int
wordIndices words = foldlWithIndex (\index table word -> Map.insert word index table) Map.empty words

letterCounts :: String -> Map Char Int
letterCounts text = foldl (\counts letter -> Map.insertWith (+) letter 1 counts) Map.empty (CodeUnits.toCharArray text)

setOfSquares :: Int -> Set Int
setOfSquares count = Set.fromFoldable (Array.range 0 count <#> \n -> n * n)

reachable :: Int -> Array Int
reachable steps = go 0 [ 1 ] (Set.delete 1 (Set.fromFoldable (Array.range 1 40)))
  where
  go step frontier unvisited
    | step == steps = Set.toUnfoldable unvisited
    | otherwise = do
        let next = Set.fromFoldable (Array.filter (_ `Set.member` unvisited) (frontier >>= \n -> [ n * 2, n + 3 ]))
        go (step + 1) (Set.toUnfoldable next) (unvisited `Set.difference` next)

withoutEvens :: Map Int Int -> Map Int Int
withoutEvens table = foldl (\kept n -> if n `mod` 2 == 0 then Map.delete n kept else Map.insert n (n * 10) kept) table (Array.range 1 14)

readThenChange :: Int -> Array Int
readThenChange count = do
  let table = squares count
  let total = totalOf table
  Map.values (Map.insert 100 total table) # List.toUnfoldable

totalOf :: Map Int Int -> Int
totalOf table = foldl (+) 0 table

keptInRecord :: Int -> { table :: Map Int Int, count :: Int }
keptInRecord count = { table: Map.insert 99 99 (squares count), count }

capturedByClosure :: Map Int Int -> Int -> Int
capturedByClosure table key = fromMaybe (-1) (Map.lookup key table)

smallestFirst :: Map Int Int -> Array Int
smallestFirst table = case Map.findMin table of
  Nothing -> []
  Just { key } -> Array.cons key (smallestFirst (Map.delete key table))

recordKeys :: Int -> Map { x :: Int, y :: Int } Int
recordKeys count = foldl (\table n -> Map.insert { x: n `mod` 3, y: n } n table) Map.empty (Array.range 1 count)
