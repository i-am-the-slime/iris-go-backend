module Repro.LensComposition where

import Prelude

import Data.Lens (Lens', view)
import Data.Lens.Record (prop)
import Effect (Effect)
import Effect.Console (log)
import Type.Proxy (Proxy(..))

_name :: forall r. Lens' { name :: String | r } String
_name = prop (Proxy @"name")

main :: Effect Unit
main = log (view _name { name: "lens" })
