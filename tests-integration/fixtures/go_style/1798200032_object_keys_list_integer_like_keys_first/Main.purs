module Repro.R01 where

-- Foreign.Object: JS enumerates integer-like keys ("0".."4294967294") first, ascending.
-- Go backend keeps pure insertion order.
import Prelude

import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Effect.Console (log)
import Foreign.Object as Object

main :: Effect Unit
main = do
  Object.fromFoldable [ "b" /\ 1, "10" /\ 2, "2" /\ 3 ] # Object.keys # show # log
  Object.fromHomogeneous { b: 1, "3": 3 } # Object.keys # show # log
