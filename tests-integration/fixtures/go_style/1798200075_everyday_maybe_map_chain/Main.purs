module Main where

import Prelude
import Effect (Effect)
import Effect.Console (log)
import Data.Maybe (Maybe(..))

main :: Effect Unit
main = do
  log "hello"
  Just 1 <#> (_ + 1) <#> (_ * 2) # show # log
