module Main where

import Prelude

import Effect (Effect)
import Effect.Aff (Aff, launchAff_)
import Effect.Class.Console (log)
import Unsafe.Coerce (unsafeCoerce)

main :: Effect Unit
main = launchAff_ do
  counted <- pretendCount (log "handled")
  log (show counted)
  where
  pretendCount :: Aff Unit -> Aff Int
  pretendCount = unsafeCoerce
