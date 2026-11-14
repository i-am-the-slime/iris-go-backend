module Compat.Records.RowList where

import Prelude

import Data.Array as Array
import Data.Symbol (class IsSymbol, reflectSymbol)
import Effect (Effect)
import Effect.Console (log)
import Prim.Row as Row
import Prim.RowList (class RowToList, RowList, Cons, Nil)
import Record as Record
import Type.Proxy (Proxy(..))

class Keys :: RowList Type -> Constraint
class Keys list where
  keysOf :: Proxy list -> Array String

instance Keys Nil where
  keysOf _ = []

instance (IsSymbol label, Keys tail) => Keys (Cons label value tail) where
  keysOf _ = Array.cons (reflectSymbol (Proxy @label)) (keysOf (Proxy @tail))

keys :: forall row list. RowToList row list => Keys list => Record row -> Array String
keys _ = keysOf (Proxy @list)

class ShowFields :: RowList Type -> Row Type -> Constraint
class ShowFields list row where
  showFields :: Proxy list -> Record row -> Array String

instance ShowFields Nil row where
  showFields _ _ = []

instance (IsSymbol label, Show value, Row.Cons label value rest row, ShowFields tail row) => ShowFields (Cons label value tail) row where
  showFields _ record = Array.cons (reflectSymbol (Proxy @label) <> ": " <> show (Record.get (Proxy @label) record)) (showFields (Proxy @tail) record)

describe :: forall row list. RowToList row list => ShowFields list row => Record row -> String
describe record = "{ " <> Array.intercalate ", " (showFields (Proxy @list) record) <> " }"

class Sized :: RowList Type -> Constraint
class Sized list where
  size :: Proxy list -> Int

instance Sized Nil where
  size _ = 0
else instance Sized (Cons label value tail) => Sized (Cons label value tail) where
  size _ = 1

class Classify a where
  classify :: a -> String

instance Classify Int where
  classify _ = "int"
else instance Classify String where
  classify _ = "string"
else instance Classify a where
  classify _ = "something else"

main :: Effect Unit
main = do
  log (show (keys { zeta: 1, alpha: "a", mid: true }))
  log (describe { name: "x", count: 3, ratio: 1.5, tags: [ "a" ] })
  log (classify 1 <> " " <> classify "s" <> " " <> classify true)
