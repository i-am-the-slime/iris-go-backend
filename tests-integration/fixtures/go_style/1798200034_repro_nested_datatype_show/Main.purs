module Repro.R03 where

-- Nested datatype (polymorphic recursion through a Show instance): JS fine, Go compiler hangs.
import Prelude

import Effect (Effect)
import Effect.Console (log)

data Nested a = Flat a | Nest (Nested (Array a))

instance Show a => Show (Nested a) where
  show (Flat a) = "Flat " <> show a
  show (Nest inner) = "Nest (" <> show inner <> ")"

main :: Effect Unit
main = log (show (Nest (Flat [ 1 ])))
