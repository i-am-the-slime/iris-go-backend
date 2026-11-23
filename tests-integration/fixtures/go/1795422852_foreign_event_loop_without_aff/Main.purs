module Main where

import Prelude

import Effect (Effect)

foreign import onAnotherGoroutine :: Effect Unit -> Effect Unit

main :: Effect Unit
main = onAnotherGoroutine (pure unit)
