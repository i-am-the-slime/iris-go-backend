module Compat.Records.Builder where

import Prelude

import Effect (Effect)
import Effect.Console (log)
import Record as Record
import Record.Builder (Builder, build, insert, merge, modify, rename, delete)
import Type.Proxy (Proxy(..))

main :: Effect Unit
main = do
  let built = build pipeline { first: "Ada", last: "Lovelace", born: 1815 }
  log (built.name <> " " <> show built.age <> " " <> built.title <> " " <> show built.verified)
  let merged = Record.merge { a: 1, b: "x" } { c: true }
  log (show merged)
  let union = Record.union { a: 1 } { a: "shadowed", z: 'z' }
  log (show union.a <> " " <> show union.z)
  log (show (Record.get (Proxy @"b") merged) <> " " <> show (Record.set (Proxy @"a") 99 merged))
  log (show (Record.insert (Proxy @"d") [ 1, 2 ] merged))
  log (show (Record.delete (Proxy @"b") merged))
  log (show (Record.rename (Proxy @"c") (Proxy @"flag") merged))
  log (show (Record.equal { x: 1, y: 2 } { x: 1, y: 2 }))
  where
  pipeline :: Builder { first :: String, last :: String, born :: Int } { name :: String, age :: Int, title :: String, verified :: Boolean }
  pipeline =
    modify (Proxy @"age") (\born -> 2025 - born)
      <<< rename (Proxy @"born") (Proxy @"age")
      <<< merge { title: "Countess" }
      <<< insert (Proxy @"verified") true
      <<< delete (Proxy @"first")
      <<< delete (Proxy @"last")
      <<< insert (Proxy @"name") "Ada Lovelace"
