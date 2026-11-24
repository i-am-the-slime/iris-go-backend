module Repro.R02 where

import Prelude

import Effect (Effect)
import Effect.Console (log)
import Unsafe.Coerce (unsafeCoerce)

-- Go: "a coercion between records with different fields (a rank-N value coerced
-- to another instantiation) is not supported". JS: record update copies all
-- runtime fields so widening back works.
main :: Effect Unit
main = do
  let wide = { name: "Ann", age: 30 }
  let updated = (unsafeCoerce wide :: { age :: Int }) { age = 31 }
  log (show (unsafeCoerce updated :: { name :: String, age :: Int }))
