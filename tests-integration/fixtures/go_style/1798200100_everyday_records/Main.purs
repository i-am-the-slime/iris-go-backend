module Fun.Records where

import Prelude

import Data.Array (sortWith, (..))
import Data.Foldable (foldl, maximumBy)
import Data.Function (on)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Effect.Console (log)
import Heterogeneous.Mapping (class MapRecordWithIndex, hmap, hmapWithIndex, class Mapping, class MappingWithIndex, ConstMapping)
import Record as Record
import Type.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)

type Person r = { name :: String, age :: Int | r }

greet :: forall r. Person r -> String
greet { name, age } = name <> " (" <> show age <> ")"

birthday :: forall r. Person r -> Person r
birthday person = person { age = person.age + 1 }

renameAll :: forall r. (String -> String) -> Array (Person r) -> Array (Person r)
renameAll f = map \person -> person { name = f person.name }

oldest :: forall r. Array (Person r) -> Maybe (Person r)
oldest = maximumBy (compare `on` _.age)

data Double = Double

instance Mapping Double Int Int where
  mapping _ = (_ * 2)

data Label = Label

instance (Show a) => MappingWithIndex Label (Proxy sym) a String where
  mappingWithIndex _ _ = show

main :: Effect Unit
main = do
  let alice = { name: "alice", age: 30, email: "a@x" }
  let bob = { name: "bob", age: 41 }
  let carol = { name: "carol", age: 25, email: "c@x", admin: true }
  log $ greet alice <> greet bob <> greet carol
  log $ show (birthday alice) <> show (birthday bob) <> show (birthday carol)
  log $ show (renameAll (_ <> "!") [ alice, alice { name = "al" } ])
  log $ show (oldest [ alice, alice { age = 99 }, alice { age = 5 } ] <#> _.age)
  log $ show (sortWith _.age [ birthday bob, bob { age = 1 }, bob ] <#> _.age)
  log $ show (Record.delete (Proxy :: Proxy "email") alice)
  log $ show (Record.rename (Proxy :: Proxy "name") (Proxy :: Proxy "fullName") bob)
  log $ show (Record.modify (Proxy :: Proxy "age") (_ * 2) carol)
  log $ show (Record.union bob { extra: [ 1 ] })
  log $ show (Record.disjointUnion bob { extra: 'x' })
  log $ show (Record.nub (Record.union { age: 1 } bob))
  log $ show (Record.set (Proxy :: Proxy "age") "now a string" bob)
  log $ show (alice == alice { age = 30 }) <> show (alice == birthday alice) <> show (compare bob (birthday bob))
  let byPerson = Map.fromFoldable [ bob /\ "b", (birthday bob) /\ "b+", bob { name = "aaa" } /\ "a" ]
  log $ show (Map.toUnfoldable byPerson :: Array _)
  log $ show (hmap Double { a: 1, b: 2, c: 3 })
  log $ show (hmapWithIndex Label { a: 1, b: "two", c: Just 3.0 })
  let nested = { outer: { inner: { deepest: 1 } }, list: [ { k: 1 }, { k: 2 } ] }
  log $ show (nested { outer { inner { deepest = 2 } } })
  log $ show (nested.list <#> _.k <#> (_ + 1))
  log $ show (foldl (\acc { k } -> acc + k) 0 nested.list)
  let coerced = unsafeCoerce { name: "x", age: 1, hidden: true } :: { name :: String, age :: Int }
  log $ greet coerced
  let accessors = [ _.age, _.age >>> (_ * 2), \p -> p.age + 100 ]
  log $ show (accessors <@> bob)
  log $ show ((1 .. 3) <#> \i -> { index: i, square: i * i, label: show i })
  log $ show { a: { b: { c: [ { d: unit } ] } } }
