module Repro.R03 where

import Prelude

import Data.Symbol (class IsSymbol, reflectSymbol)
import Data.Variant (Unvariant(..), Variant, inj, unvariant)
import Effect (Effect)
import Effect.Console (log)
import Type.Proxy (Proxy(..))

-- Go: "cannot specialize Data.Variant.unvariant: constrained types in argument
-- positions is not supported by the Go backend yet"
labelName :: forall r. Variant r -> String
labelName v = case unvariant v of
  Unvariant run -> run \proxy _ -> reflectSymbol proxy

-- Local analog with an IsSymbol-constrained rank-2 continuation (works on Go)
newtype Labelled = Labelled (forall x. (forall s. IsSymbol s => Proxy s -> x) -> x)

mkLabelled :: forall @s. IsSymbol s => Labelled
mkLabelled = Labelled \k -> k (Proxy @s)

labelledName :: Labelled -> String
labelledName (Labelled run) = run reflectSymbol

main :: Effect Unit
main = do
  log (labelName (inj (Proxy @"circle") 1.5 :: Variant (circle :: Number)))
  log (labelledName (mkLabelled @"local"))
