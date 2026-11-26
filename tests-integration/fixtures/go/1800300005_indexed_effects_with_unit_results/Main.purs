module Main where

import Prelude

import Data.TraversableWithIndex (forWithIndex)
import Effect (Effect)
import Journal (log)

main :: Effect Unit
main = do
  units <- forWithIndex [ "a", "b" ] \index letter -> log (show index <> letter)
  log (show units)
