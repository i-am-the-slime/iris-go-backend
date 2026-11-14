module Repro.RecordUnionDuplicate where

import Prelude

import Effect (Effect)
import Effect.Console (log)
import Record as Record

main :: Effect Unit
main = do
  let union = Record.union { a: 1 } { a: "shadowed", z: 'z' }
  log (show union.a <> " " <> show union.z)
