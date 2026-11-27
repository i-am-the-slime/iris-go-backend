module Main where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))

-- | Keeps the newest keys by when they came, evicting the oldest once there are too many.
type Recent = { clock :: Int, byTime :: Map Int Int }

remember :: Int -> Recent -> Recent
remember key recent = do
  let added = recent.byTime # Map.insert recent.clock key
  let kept = case Map.findMin added of
        Just { key: oldest } | Map.size added > 8 -> Map.delete oldest added
        _ -> added
  { clock: recent.clock + 1, byTime: kept }

main :: Int
main = case Map.lookupGE 100 recent.byTime of
  Just { value } -> value
  Nothing -> Map.size recent.byTime
  where
  recent = Array.range 1 200 <#> (_ `mod` 37) # foldl (flip remember) { clock: 0, byTime: Map.empty }
