module Main where

import Prelude

import Effect (Effect)
import Journal (log)
import Unsafe.Coerce (unsafeCoerce)

type Person = { name :: String, age :: Int }

main :: Effect Unit
main = do
  let people = [ { name: "Ann", age: 30 }, { name: "Bo", age: 41 } ]
  let narrowed = map (\person -> (unsafeCoerce person :: { age :: Int }) { age = 31 }) people
  log (show (map (\person -> unsafeCoerce person :: Person) narrowed))
