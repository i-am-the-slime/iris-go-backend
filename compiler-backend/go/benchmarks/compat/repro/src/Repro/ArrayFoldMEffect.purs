module Repro.ArrayFoldMEffect where

import Prelude

import Data.Array as Array
import Effect (Effect)
import Effect.Console (log)

main :: Effect Unit
main = do
  total <- Array.foldM (\acc n -> log (show n) $> (acc + n)) 0 [ 1, 2, 3 ]
  log (show total)
