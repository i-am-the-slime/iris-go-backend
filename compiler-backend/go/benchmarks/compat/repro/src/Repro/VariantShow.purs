module Repro.VariantShow where

import Prelude

import Data.Variant (Variant, inj)
import Effect (Effect)
import Effect.Console (log)
import Type.Proxy (Proxy(..))

main :: Effect Unit
main = log (show (inj (Proxy @"number") 1 :: Variant (number :: Int, text :: String)))
