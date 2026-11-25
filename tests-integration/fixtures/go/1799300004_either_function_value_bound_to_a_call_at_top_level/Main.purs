module Main where

import Prelude

import Data.Either (Either(..))
import Data.List (List(..), (:))
import Data.Traversable (sequence)
import Effect (Effect)
import Journal (log)

main :: Effect Unit
main = do
  log (show (sequence (Right 1 : Left "x" : Nil :: List (Either String Int))))
  log (show (sequence (Right 1 : Right 2 : Nil :: List (Either String Int))))
