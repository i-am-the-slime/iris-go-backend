module Compat.Records.TypeLevel where

import Prelude

import Data.Reflectable (class Reflectable, reflectType)
import Data.Symbol (class IsSymbol, reflectSymbol)
import Effect (Effect)
import Effect.Console (log)
import Prim.Row as Row
import Prim.Symbol as Symbol
import Record as Record
import Type.Equality (class TypeEquals, to, from)
import Type.Proxy (Proxy(..))

withDefaults :: forall given merged. Row.Union given (port :: Int, host :: String) merged => Row.Nub merged (port :: Int, host :: String) => Record given -> { port :: Int, host :: String }
withDefaults given = Record.merge given { port: 80, host: "example.org" }

addId :: forall row. Row.Lacks "id" row => Record row -> Record (id :: Int | row)
addId = Record.insert (Proxy @"id") 1

joined :: forall left right both. Symbol.Append left right both => IsSymbol both => Proxy left -> Proxy right -> String
joined _ _ = reflectSymbol (Proxy @both)

newtype Wrapper a = Wrapper a

unwrapEqual :: forall a b. TypeEquals a Int => Wrapper a -> b -> Int
unwrapEqual (Wrapper a) _ = to a + 1

class Describe a where
  describe :: a -> String

instance TypeEquals a String => Describe (Array a) where
  describe values = "strings: " <> show (map to values)

reflectNumber :: forall @n. Reflectable n Int => Int
reflectNumber = reflectType (Proxy @n)

main :: Effect Unit
main = do
  log (show (withDefaults { port: 8080 }))
  log (show (withDefaults {}))
  log (show (addId { name: "n" }))
  log (joined (Proxy @"type") (Proxy @"level"))
  log (show (unwrapEqual (Wrapper 41) unit))
  log (describe [ "a", "b" ])
  log (show (reflectNumber @42 + 1))
  log (show (from 3 :: Int))
