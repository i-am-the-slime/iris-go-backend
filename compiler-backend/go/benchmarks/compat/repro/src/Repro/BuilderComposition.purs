module Repro.BuilderComposition where

import Prelude

import Effect (Effect)
import Effect.Console (log)
import Record.Builder (Builder, build, insert, rename)
import Type.Proxy (Proxy(..))

pipeline :: Builder { born :: Int } { age :: Int, title :: String }
pipeline = rename (Proxy @"born") (Proxy @"age") <<< insert (Proxy @"title") "Countess"

main :: Effect Unit
main = log (show (build pipeline { born: 1815 }))
