module Repro.R04 where

import Prelude

import Data.Variant (Variant, inj, over)
import Effect (Effect)
import Effect.Console (log)
import Type.Proxy (Proxy(..))

-- Go: `go build` fails inside Data.Variant.over (also overSome / traverse):
-- cannot use shared.VariantRepOfValue{…} as shared.VariantRepVariantCase value in assignment
main :: Effect Unit
main = do
  let doubled = over { n: (_ * 2) } (inj (Proxy @"n") 21 :: Variant (n :: Int))
  log (show doubled)
