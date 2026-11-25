module Main where

import Prelude

import Data.Foldable (for_, sequence_, traverse_)
import Data.FoldableWithIndex (traverseWithIndex_)
import Effect (Effect)
import Journal (log)

main :: Effect Unit
main = do
  log (show (traverse_ (\x -> [x, x + 1]) [1, 2]))
  log (show (for_ [1, 2, 3] (\x -> [x])))
  log (show (sequence_ [[1], [2, 3]]))
  log (show (traverseWithIndex_ (\i x -> [i, x]) [5, 6]))
  log (show ([\_ -> unit, \_ -> unit] <*> [1, 2, 3]))
