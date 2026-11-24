module TL.Symbols where

import Prelude

import Data.Symbol (class IsSymbol, reflectSymbol)
import Data.Reflectable (class Reflectable, reflectType)
import Effect (Effect)
import Effect.Console (log)
import Prim.Row as Row
import Prim.Symbol as Symbol
import Record as Record
import Type.Proxy (Proxy(..))
import Prim.Int as Int

reflectThing :: forall @s. IsSymbol s => String
reflectThing = reflectSymbol (Proxy @s)

appended :: forall @l @r out. Symbol.Append l r out => IsSymbol out => String
appended = reflectSymbol (Proxy @out)

headOf :: forall @s h t. Symbol.Cons h t s => IsSymbol h => String
headOf = reflectSymbol (Proxy @h)

tailOf :: forall @s h t. Symbol.Cons h t s => IsSymbol t => String
tailOf = reflectSymbol (Proxy @t)

-- Prefix: compute "get" <> capitalised? just prefix
class Prefixed (prefix :: Symbol) (label :: Symbol) (out :: Symbol) | prefix label -> out
instance Symbol.Append prefix label out => Prefixed prefix label out

getterName :: forall @label out. Prefixed "get_" label out => IsSymbol out => String
getterName = reflectSymbol (Proxy @out)

-- Reverse a symbol at the type level
class ReverseSymbol (s :: Symbol) (acc :: Symbol) (out :: Symbol) | s acc -> out
instance ReverseSymbol "" acc acc
else instance (Symbol.Cons h t s, Symbol.Cons h acc acc2, ReverseSymbol t acc2 out) => ReverseSymbol s acc out

reversed :: forall @s out. ReverseSymbol s "" out => IsSymbol out => String
reversed = reflectSymbol (Proxy @out)

-- Symbol length via Int arithmetic
class SymbolLength (s :: Symbol) (n :: Int) | s -> n
instance SymbolLength "" 0
else instance (Symbol.Cons h t s, SymbolLength t m, Int.Add m 1 n) => SymbolLength s n

lengthOf :: forall @s n. SymbolLength s n => Reflectable n Int => Int
lengthOf = reflectType (Proxy @n)

-- Lacks / Nub / Union
addField :: forall @label a r1 r2. IsSymbol label => Row.Lacks label r1 => Row.Cons label a r1 r2 => a -> Record r1 -> Record r2
addField = Record.insert (Proxy @label)

mergeNubbed :: forall r1 r2 r3 r4. Row.Union r1 r2 r3 => Row.Nub r3 r4 => Record r1 -> Record r2 -> Record r4
mergeNubbed = Record.merge

renameField :: forall @from @to a r rFrom rTo. IsSymbol from => IsSymbol to => Row.Cons from a r rFrom => Row.Lacks from r => Row.Cons to a r rTo => Row.Lacks to r => Record rFrom -> Record rTo
renameField = Record.rename (Proxy @from) (Proxy @to)

class Named a where
  nameOf :: Proxy a -> String

instance Named Int where
  nameOf _ = "Int"

instance Named String where
  nameOf _ = "String"

instance (Named a, Named b) => Named (a -> b) where
  nameOf _ = nameOf (Proxy @a) <> " -> " <> nameOf (Proxy @b)

nameOfType :: forall @a. Named a => String
nameOfType = nameOf (Proxy @a)

main :: Effect Unit
main = do
  log (reflectThing @"hello")
  log (reflectThing @"ünïcödé ✓")
  log (appended @"foo" @"Bar")
  log (headOf @"xyz")
  log (tailOf @"xyz")
  log (headOf @"äbc")
  log (getterName @"name")
  log (reversed @"stressed")
  log (reversed @"añb")
  log (show (lengthOf @"hello"))
  log (show (lengthOf @""))
  log (show (reflectType (Proxy @42) :: Int))
  log (show (addField @"z" true { a: 1 }))
  log (show (mergeNubbed { a: 1, b: "x" } { b: "y", c: 3.5 }))
  log (show (renameField @"a" @"alpha" { a: 1, b: 2 }))
  log (nameOfType @(Int -> String -> Int))
  log (show (Record.delete (Proxy @"b") { a: 1, b: 2, c: 3 }))
  log (show (Record.modify (Proxy @"a") (_ + 41) { a: 1 }))
  log (show (Record.equal { a: 1, b: "x" } { a: 1, b: "x" }))
