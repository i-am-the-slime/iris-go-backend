module Repro.R15 where

import Prelude

import Effect (Effect)
import Effect.Console (log)

main :: Effect Unit
main = log "hello"
  where
  _ = show
