module Main where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Set (Set)
import Data.Set as Set
import Data.Tuple.Nested (type (/\), (/\))
import Effect (Effect)
import Effect.Console (log)

type Graph = Map Int (Array (Int /\ Int))

graph :: Int -> Graph
graph n = Map.fromFoldable (Array.range 0 (n - 1) <#> \node -> node /\ [ ((node * 7 + 1) `mod` n) /\ (1 + node `mod` 5), ((node * 3 + 2) `mod` n) /\ (2 + node `mod` 7) ])

shortest :: Graph -> Int -> Map Int Int
shortest edges source = go (Set.singleton (0 /\ source)) (Map.singleton source 0)
  where
  go :: Set (Int /\ Int) -> Map Int Int -> Map Int Int
  go frontier distances = case Set.findMin frontier of
    Nothing -> distances
    Just (distance /\ node) -> do
      let rest = Set.delete (distance /\ node) frontier
      let step (open /\ known) (next /\ weight) = do
            let candidate = distance + weight
            if candidate < fromMaybe 1000000000 (Map.lookup next known) then Set.insert (candidate /\ next) open /\ Map.insert next candidate known else open /\ known
      let open /\ known = foldl step (rest /\ distances) (fromMaybe [] (Map.lookup node edges))
      go open known

labelled :: Int -> Map { row :: Int, word :: String } Int
labelled n = go (Map.singleton { row: 0, word: "start" } 0) 1
  where
  go table k
    | k > n = table
    | otherwise = case Map.findMin table of
        Just { key } -> go (Map.insert { row: (k * 37) `mod` 11, word: "w" <> show (k `mod` 4) } k (Map.delete key table)) (k + 1)
        Nothing -> table

main :: Effect Unit
main = do
  let distances = shortest (graph 200) 0
  log (show (Map.size distances))
  log (show (foldl (+) 0 distances))
  log (show (Array.take 12 (Map.toUnfoldable distances :: Array _)))
  log (show (Map.toUnfoldable (labelled 30) :: Array _))
