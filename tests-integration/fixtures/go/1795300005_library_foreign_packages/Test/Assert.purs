module Test.Assert (assert') where

import Prelude

import Effect (Effect)

assert' :: String -> Boolean -> Effect Unit
assert' = assertImpl

foreign import assertImpl :: String -> Boolean -> Effect Unit
