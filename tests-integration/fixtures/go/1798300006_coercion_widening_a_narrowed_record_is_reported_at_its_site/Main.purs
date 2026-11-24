module Main where

import Prelude

import Effect (Effect)
import Journal (log)
import Unsafe.Coerce (unsafeCoerce)

main :: Effect Unit
main = do
  let wide = { name: "Ann", age: 30 }
  let updated = (unsafeCoerce wide :: { age :: Int }) { age = 31 }
  log (show (unsafeCoerce updated :: { name :: String, age :: Int }))
