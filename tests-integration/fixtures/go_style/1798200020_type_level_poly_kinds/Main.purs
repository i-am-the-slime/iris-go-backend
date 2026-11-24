module TL.PolyKind where

import Prelude

import Data.Either (Either)
import Data.Maybe (Maybe(..))
import Data.Symbol (class IsSymbol, reflectSymbol)
import Data.Variant (Variant)
import Effect (Effect)
import Effect.Console (log)
import Type.Proxy (Proxy(..))
import Prim.RowList as RL
import Record.Unsafe.Union (unsafeUnion)

class TypeName :: forall k. k -> Constraint
class TypeName a where
  typeName :: Proxy a -> String

instance TypeName Int where
  typeName _ = "Int"
else instance TypeName String where
  typeName _ = "String"
else instance TypeName Maybe where
  typeName _ = "Maybe"
else instance TypeName Either where
  typeName _ = "Either"
else instance TypeName "sym" where
  typeName _ = "the symbol sym"
else instance TypeName 42 where
  typeName _ = "forty-two"
else instance (TypeName f, TypeName a) => TypeName (f a) where
  typeName _ = "(" <> typeName (Proxy @f) <> " " <> typeName (Proxy @a) <> ")"
else instance TypeName a where
  typeName _ = "?"

nameOf :: forall @a. TypeName a => String
nameOf = typeName (Proxy @a)

-- poly-kinded proxy-holding newtype
newtype Tagged :: forall k. k -> Type -> Type
newtype Tagged tag a = Tagged a

retag :: forall @t2 t1 a. Tagged t1 a -> Tagged t2 a
retag (Tagged a) = Tagged a

describeTagged :: forall tag a. TypeName tag => Show a => Tagged tag a -> String
describeTagged (Tagged a) = typeName (Proxy @tag) <> ":" <> show a

-- RowList kind
class CountRL :: forall k. RL.RowList k -> Constraint
class CountRL rl where
  countRL :: Proxy rl -> Int

instance CountRL RL.Nil where
  countRL _ = 0

instance CountRL tail => CountRL (RL.Cons label v tail) where
  countRL _ = 1 + countRL (Proxy @tail)

countRow :: forall @r rl. RL.RowToList r rl => CountRL rl => Int
countRow = countRL (Proxy @rl)

main :: Effect Unit
main = do
  log (nameOf @Int)
  log (nameOf @(Maybe Int))
  log (nameOf @(Either String (Maybe Int)))
  log (nameOf @Either)
  log (nameOf @(Either String))
  log (nameOf @"sym")
  log (nameOf @"other")
  log (nameOf @42)
  log (nameOf @Boolean)
  log (nameOf @(Proxy "sym"))
  log (describeTagged (Tagged 5 :: Tagged "sym" Int))
  log (describeTagged (retag @Maybe (Tagged "x" :: Tagged 42 String)))
  log (show (countRow @(a :: Int, b :: String, c :: Unit)))
  log (show (unsafeUnion { a: 1 } { b: "two" } :: { a :: Int, b :: String }))
  log (show (unsafeUnion { a: 1, b: "left" } { b: "right", c: true } :: { a :: Int, b :: String, c :: Boolean }))
