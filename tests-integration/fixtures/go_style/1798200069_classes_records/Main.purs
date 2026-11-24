module T.Records where

import Prelude

import Data.Array as Array
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Effect.Console (log)
import Record as Record
import Record.Builder as Builder
import Type.Proxy (Proxy(..))
import Data.Symbol (class IsSymbol)
import Prim.Row as Row

greet :: forall r. { name :: String | r } -> String
greet person = "hi " <> person.name

greetBoth :: forall r. { name :: String, age :: Int | r } -> String
greetBoth { name, age } = name <> "@" <> show age

rename' :: forall r. { name :: String | r } -> { name :: String | r }
rename' = _ { name = "renamed" }

type Big =
  { f01 :: Int, f02 :: Int, f03 :: String, f04 :: Number, f05 :: Boolean
  , f06 :: Int, f07 :: Int, f08 :: String, f09 :: Number, f10 :: Boolean
  , f11 :: Int, f12 :: Int, f13 :: String, f14 :: Number, f15 :: Boolean
  , f16 :: Int, f17 :: Int, f18 :: String, f19 :: Number, f20 :: Boolean
  , f21 :: Array Int, f22 :: Maybe Int, a :: Int, z :: Int
  }

big :: Big
big =
  { f01: 1, f02: 2, f03: "three", f04: 4.0, f05: true
  , f06: 6, f07: 7, f08: "eight", f09: 9.5, f10: false
  , f11: 11, f12: 12, f13: "thirteen", f14: 14.25, f15: true
  , f16: 16, f17: 17, f18: "eighteen", f19: -19.0, f20: false
  , f21: [ 21 ], f22: Just 22, a: 0, z: 26
  }

main :: Effect Unit
main = do
  let ada = { name: "Ada", age: 36 }
  let bob = { name: "Bob", age: 41, email: "b@x" }
  let cat = { name: "Cat", lives: 9, owner: { name: "Dee", address: { city: "Oslo", zip: 1 } } }
  log (greet ada <> greet bob <> greet cat <> greet cat.owner)
  log (greetBoth ada <> greetBoth bob)
  log (show (rename' bob) <> show (rename' ada))
  [ ada, ada { age = 1 }, ada { name = "Z" } ] <#> _ { age = 99 } <#> greetBoth # show # log
  [ ada, bob { name = "b" } # deleteField @"email" ] <#> _.name # show # log
  let moved = cat { owner { address { city = "Bergen" }, name = "Eve" }, lives = 8 }
  log (show moved)
  log (show cat)
  log (show (Record.merge ada { email: "a@x", age: 1000 }))
  log (show (insertField @"id" 7 ada) <> show (Record.insert (Proxy :: _ "id") 7 ada))
  log (show (deleteField @"age" bob) <> show (Record.delete (Proxy :: _ "age") bob))
  log (show (getField @"email" bob) <> show (Record.get (Proxy :: _ "email") bob))
  log (show (setField @"age" "old" ada) <> show (Record.set (Proxy :: _ "age") "old" ada))
  log (show (modifyField @"age" (_ * 2) ada) <> show (Record.modify (Proxy :: _ "age") show ada))
  log (show (renameField @"name" @"title" ada) <> show (Record.rename (Proxy :: _ "name") (Proxy :: _ "title") ada))
  log (show (Record.equal ada { name: "Ada", age: 36 }))
  let built = Builder.build (Builder.insert (Proxy :: _ "x") 1 >>> Builder.modify (Proxy :: _ "name") (_ <> "!") >>> Builder.delete (Proxy :: _ "age") >>> Builder.merge { y: 2.5 }) ada
  log (show built)
  log (show (Builder.buildFromScratch (Builder.insert (Proxy :: _ "only") true)))
  log (show {} <> show { one: 1 } <> show { "quoted key": 1, "with\"quote": 2 })
  log (show big)
  log (show (big { f10 = true, a = -1 }).f10 <> show (big == big) <> show (compare big (big { f01 = 0 })))
  let keyed = Map.fromFoldable [ { x: 1, y: 2 } /\ "a", { x: 0, y: 5 } /\ "b", { x: 1, y: -1 } /\ "c" ]
  log (show keyed)
  log (show (Map.lookup { x: 1, y: -1 } keyed))
  let valued = Map.fromFoldable [ "k1" /\ ada, "k0" /\ ada { age = 0 } ]
  log (show valued)
  log (show (Set.fromFoldable [ { a: 2 }, { a: 1 }, { a: 2 } ]))
  log (show (ada == { name: "Ada", age: 36 }) <> show (ada < { name: "Ada", age: 37 }) <> show (compare { a: 1, b: "x" } { a: 1, b: "w" }))
  log (show (Array.sortWith _.age [ ada, bob # deleteField @"email", { name: "Neg", age: -5 } ]))
  log (show { n: 1.0, m: 0.1 + 0.2, k: 1.0e-10, j: 123456789.0, i: -0.5, h: 1.0 / 0.0 })
  log (show [ { nested: [ { deep: Just { deeper: [ 1 ] } } ] } ])

getField :: forall @l r r' a. IsSymbol l => Row.Cons l a r' r => Record r -> a
getField = Record.get (Proxy @l)

insertField :: forall @l a r r'. IsSymbol l => Row.Lacks l r => Row.Cons l a r r' => a -> Record r -> Record r'
insertField = Record.insert (Proxy @l)

deleteField :: forall @l a r r'. IsSymbol l => Row.Lacks l r => Row.Cons l a r r' => Record r' -> Record r
deleteField = Record.delete (Proxy @l)

setField :: forall @l a b r r1 r2. IsSymbol l => Row.Cons l a r r1 => Row.Cons l b r r2 => b -> Record r1 -> Record r2
setField = Record.set (Proxy @l)

modifyField :: forall @l a b r r1 r2. IsSymbol l => Row.Cons l a r r1 => Row.Cons l b r r2 => (a -> b) -> Record r1 -> Record r2
modifyField = Record.modify (Proxy @l)

renameField :: forall @prev @next ty input inter output. IsSymbol prev => IsSymbol next => Row.Cons prev ty inter input => Row.Lacks prev inter => Row.Cons next ty inter output => Row.Lacks next inter => Record input -> Record output
renameField = Record.rename (Proxy @prev) (Proxy @next)
