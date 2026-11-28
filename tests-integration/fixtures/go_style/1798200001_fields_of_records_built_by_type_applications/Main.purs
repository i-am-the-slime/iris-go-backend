module Repro.R01 where

import Prelude

import Effect (Effect)
import Effect.Console (log)
import Data.Symbol (class IsSymbol, reflectSymbol)
import Type.Proxy (Proxy(..))

-- `(f @T).field` on a constrained value drops the dictionaries:
-- JS prints "undefined" / crashes, Go refuses to specialize.
zeroOf :: forall @a. Monoid a => Show a => { shown :: String }
zeroOf = { shown: show (mempty :: a) }

class Def a where
  def :: { v :: a }

instance Def Int where
  def = { v: 7 }

main :: Effect Unit
main = do
  log (zeroOf @String # _.shown)
  log (zeroOf @String).shown
  log (show (def :: { v :: Int }).v)
  log (show (def @Int).v)
  let z = zeroOf @(Array Int)
  log z.shown
  -- JS prints the JS function's own `.name` ("recordOf") instead of "chained"
  log (recordOf @"chained").name
  where
  recordOf :: forall @s. IsSymbol s => { name :: String }
  recordOf = { name: reflectSymbol (Proxy @s) }
