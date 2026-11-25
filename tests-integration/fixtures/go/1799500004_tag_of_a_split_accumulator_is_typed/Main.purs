module Main where

import Prelude

import Data.Foldable (foldl)
import Distances (Distance(..), measured)
import Effect (Effect)
import Journal (log)

farthest :: Array Int -> Distance
farthest = foldl (\best n -> let d = measured n in if d > best then d else best) None

main :: Effect Unit
main = do
  log (show (farthest [3, -1, 5, 2]))
  log (show (farthest [-1]))
