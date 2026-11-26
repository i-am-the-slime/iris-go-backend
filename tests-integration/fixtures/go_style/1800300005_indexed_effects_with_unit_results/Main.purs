module Main where

import Prelude

import Data.TraversableWithIndex (forWithIndex)
import Effect (Effect)
import Effect.Console (log, logShow)

main :: Effect Unit
main = do
  units <- forWithIndex [ "a", "b" ] \index letter -> log (show index <> letter)
  logShow units
