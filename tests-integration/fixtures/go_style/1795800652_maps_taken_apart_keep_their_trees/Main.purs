module Fun.TakenApart where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Map (Map)
import Data.Map as Map
import Data.Map.Internal (Map(..))
import Data.Tuple.Nested (type (/\))
import Effect (Effect)
import Effect.Console (log)

main :: Effect Unit
main = do
  log "-- a tree that the program takes apart keeps the shape its inserts gave it"
  log (show (rootKey (ascending 15)))
  log (show (rootKey (ascending 6)))
  log (show (leftDepth (ascending 20)))
  log (show (Map.toUnfoldable (ascending 6) :: Array (Int /\ Int)))

ascending :: Int -> Map Int Int
ascending count = foldl (\table n -> Map.insert n (n * n) table) Map.empty (Array.range 1 count)

rootKey :: Map Int Int -> Int
rootKey = case _ of
  Node _ _ key _ _ _ -> key
  Leaf -> 0

leftDepth :: Map Int Int -> Int
leftDepth = case _ of
  Node _ _ _ _ left _ -> 1 + leftDepth left
  Leaf -> 0
