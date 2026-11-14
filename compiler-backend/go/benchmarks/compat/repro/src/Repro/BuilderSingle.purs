module Repro.BuilderSingle where

import Prelude

import Effect (Effect)
import Effect.Console (log)
import Record.Builder (build, merge, modify, delete)
import Type.Proxy (Proxy(..))

main :: Effect Unit
main = do
  log (show (build (merge { title: "Countess" }) { born: 1815 }))
  log (show (build (modify (Proxy @"born") (_ + 1)) { born: 1815 }))
  log (show (build (delete (Proxy @"born")) { born: 1815, name: "Ada" }))
