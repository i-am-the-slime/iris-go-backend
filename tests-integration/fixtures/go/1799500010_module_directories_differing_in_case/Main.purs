module Main where

import Prelude

import Effect (Effect)
import Journal (log)
import Lib.JSON (doubled)
import Lib.Json.Extra (tripled)

main :: Effect Unit
main = do
  log (show (doubled 0 5))
  log (show (tripled 0 5))
