module Repro.R02 where

-- Data.HashMap (unordered-collections) has no Go representation in this compiler build.
import Prelude

import Data.HashMap as HashMap
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Effect.Console (log)

main :: Effect Unit
main = HashMap.fromArray [ "x" /\ 1 ] # HashMap.lookup "x" # show # log
