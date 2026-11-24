module TL.Printf where

import Prelude

import Data.Symbol (class IsSymbol, reflectSymbol)
import Effect (Effect)
import Effect.Console (log)
import Prim.Symbol as Symbol
import Type.Proxy (Proxy(..))

-- Type-level format string parsing
data FList
foreign import data FNil :: FList
foreign import data FLit :: Symbol -> FList -> FList
foreign import data FInt :: FList -> FList
foreign import data FStr :: FList -> FList

class Parse (s :: Symbol) (out :: FList) | s -> out
instance Parse "" FNil
else instance (Symbol.Cons h t s, ParseChar h t out) => Parse s out

class ParseChar (h :: Symbol) (t :: Symbol) (out :: FList) | h t -> out
instance (Symbol.Cons next rest t, ParsePercent next rest out) => ParseChar "%" t out
else instance (Parse t restOut) => ParseChar h t (FLit h restOut)

class Format (f :: FList) (fn :: Type) | f -> fn where
  format :: Proxy f -> String -> fn

instance Format FNil String where
  format _ acc = acc

instance Format rest fn => Format (FInt rest) (Int -> fn) where
  format _ acc = \n -> format (Proxy @rest) (acc <> show n)

instance Format rest fn => Format (FStr rest) (String -> fn) where
  format _ acc = \s -> format (Proxy @rest) (acc <> s)

instance (IsSymbol lit, Format rest fn) => Format (FLit lit rest) fn where
  format _ acc = format (Proxy @rest) (acc <> reflectSymbol (Proxy @lit))

printf :: forall @s parsed fn. Parse s parsed => Format parsed fn => fn
printf = format (Proxy @parsed) ""

class ParsePercent (next :: Symbol) (rest :: Symbol) (out :: FList) | next rest -> out
instance Parse rest restOut => ParsePercent "d" rest (FInt restOut)
else instance Parse rest restOut => ParsePercent "s" rest (FStr restOut)
else instance Parse rest restOut => ParsePercent next rest (FLit next restOut)

-- Open-row polymorphism
getName :: forall r. { name :: String | r } -> String
getName = _.name

setName :: forall r. String -> { name :: String | r } -> { name :: String | r }
setName newName record = record { name = newName }

bumpAll :: forall r. { count :: Int, name :: String | r } -> { count :: Int, name :: String | r }
bumpAll record = record { count = record.count + 1, name = record.name <> "+" }

-- Higher-order: pass a printf-produced function around
applyTwice :: (Int -> String) -> Array String
applyTwice f = [ f 1, f 2 ]

main :: Effect Unit
main = do
  log (printf @"hello")
  log (printf @"n=%d" 42)
  log (printf @"%s is %d years, %s" "Ann" 33 "ok")
  log (printf @"100%% %d" 5)
  let formatter = printf @"[%d]" :: Int -> String
  log (show (applyTwice formatter))
  log (show (applyTwice (printf @"<%d>")))
  log (getName { name: "a" })
  log (getName { name: "b", age: 1 })
  log (getName { name: "c", age: 1, extra: [ true ] })
  log (show (setName "z" { name: "a", age: 9 }))
  log (show (setName "z" { name: "a" }))
  log (show (bumpAll { count: 1, name: "n", flag: false }))
  log (show (bumpAll (bumpAll { count: 1, name: "n" })))
  log (show ([ { name: "x", v: 1 }, { name: "y", v: 2 } ] <#> setName "q" <#> getName))
