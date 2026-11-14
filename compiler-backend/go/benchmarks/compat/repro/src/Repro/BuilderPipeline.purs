module Repro.BuilderPipeline where

import Prelude

import Effect (Effect)
import Effect.Console (log)
import Record.Builder (Builder, build, insert, merge, modify, rename, delete)
import Type.Proxy (Proxy(..))

pipeline :: Builder { first :: String, last :: String, born :: Int } { name :: String, age :: Int, title :: String, verified :: Boolean }
pipeline =
  modify (Proxy @"age") (\born -> 2025 - born)
    <<< rename (Proxy @"born") (Proxy @"age")
    <<< merge { title: "Countess" }
    <<< insert (Proxy @"verified") true
    <<< delete (Proxy @"first")
    <<< delete (Proxy @"last")
    <<< insert (Proxy @"name") "Ada Lovelace"

main :: Effect Unit
main = log (show (build pipeline { first: "Ada", last: "Lovelace", born: 1815 }))
