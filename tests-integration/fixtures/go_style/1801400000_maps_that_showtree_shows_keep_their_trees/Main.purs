module Fun.ShownTrees where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Map (Map)
import Data.Map as Map
import Data.Map.Internal (showTree)
import Effect (Effect)
import Effect.Console (log)

main :: Effect Unit
main = do
  log "-- a map that showTree shows keeps the shape its inserts and deletes gave it"
  log (showTree (labelled 7))

labelled :: Int -> Map Int String
labelled count = foldl step Map.empty (Array.range 1 count)
  where
  step map n = if n `mod` 3 == 0 then Map.insert (n * 2) (show n) (Map.delete (n - 1) map) else Map.insert (n * 2) (show n) map
