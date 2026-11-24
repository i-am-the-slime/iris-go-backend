module TL.Labels where

import Prelude

import Data.Array as Array
import Data.Symbol (class IsSymbol, reflectSymbol)
import Data.Variant (Variant, inj, match, on, case_)
import Effect (Effect)
import Effect.Console (log)
import Prim.RowList as RL
import Record as Record
import Record.Unsafe (unsafeGet, unsafeSet, unsafeHas)
import Type.Proxy (Proxy(..))

class FieldNames (rl :: RL.RowList Type) where
  fieldNames :: Proxy rl -> Array String

instance FieldNames RL.Nil where
  fieldNames _ = []

instance (IsSymbol label, FieldNames tail) => FieldNames (RL.Cons label ty tail) where
  fieldNames _ = fieldNames (Proxy @tail) # Array.cons (reflectSymbol (Proxy @label))

namesOf :: forall r rl. RL.RowToList r rl => FieldNames rl => Record r -> Array String
namesOf _ = fieldNames (Proxy @rl)

type Weird =
  { name :: Int
  , "Name" :: Int
  , "NAME" :: String
  , "type" :: Int
  , "func" :: String
  , "with space" :: Boolean
  , "123" :: Int
  , "_" :: Int
  , "ünï" :: Int
  , "a\"quote" :: Int
  , "back\\slash" :: Int
  , "" :: Int
  , "x_y" :: Int
  , "xY" :: Int
  , "XY" :: Int
  , "map" :: Int
  , "String" :: Int
  , "nil" :: Int
  , "len" :: Int
  }

weird :: Weird
weird =
  { name: 1
  , "Name": 2
  , "NAME": "three"
  , "type": 4
  , "func": "five"
  , "with space": true
  , "123": 7
  , "_": 8
  , "ünï": 9
  , "a\"quote": 10
  , "back\\slash": 11
  , "": 12
  , "x_y": 13
  , "xY": 14
  , "XY": 15
  , "map": 16
  , "String": 17
  , "nil": 18
  , "len": 19
  }

type WeirdV = Variant ("Ok" :: Int, ok :: Int, "OK" :: String, "type" :: Unit, "" :: Int)

describeV :: WeirdV -> String
describeV = match
  { "Ok": \n -> "Ok " <> show n
  , ok: \n -> "ok " <> show n
  , "OK": \s -> "OK " <> s
  , "type": \_ -> "type"
  , "": \n -> "empty " <> show n
  }

main :: Effect Unit
main = do
  log (show weird)
  log (show (namesOf weird))
  log (show weird.name <> show weird."Name" <> weird."NAME")
  log (show (weird { "Name" = 200, name = 100 }))
  log (show (Record.get (Proxy @"XY") weird + Record.get (Proxy @"xY") weird + weird."x_y"))
  log (show (unsafeGet "Name" weird :: Int))
  log (show (unsafeHas "NAME" weird))
  log (show (unsafeHas "nope" weird))
  log (show (unsafeSet "xY" 99 weird :: Weird))
  log (describeV (inj (Proxy @"Ok") 1))
  log (describeV (inj (Proxy @"ok") 2))
  log (describeV (inj (Proxy @"OK") "3"))
  log (describeV (inj (Proxy @"type") unit))
  log (describeV (inj (Proxy @"") 5))
  log (show (inj (Proxy @"OK") "s" :: WeirdV))
  log (show ((inj (Proxy @"Ok") 1 :: WeirdV) == inj (Proxy @"ok") 1))
  log (show (weird == weird { "" = 12 }))
  log (show (weird == weird { "" = 13 }))
