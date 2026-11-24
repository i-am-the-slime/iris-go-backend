module T.RowPoly where

import Prelude

import Data.Array as Array
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Effect.Console (log)
import Prim.Row as Row
import Record as Record
import Type.Proxy (Proxy(..))

bump :: forall r. { count :: Int | r } -> { count :: Int | r }
bump = _ { count = _ } <*> (_.count >>> (_ + 1))

bump' :: forall r. { count :: Int | r } -> { count :: Int | r }
bump' record = record { count = record.count + 1 }

withId :: forall r. Row.Lacks "id" r => Int -> { | r } -> { id :: Int | r }
withId = Record.insert (Proxy @"id")

withDefaults :: forall given all. Row.Union given (color :: String, size :: Int) all => Row.Nub all (color :: String, size :: Int) => { | given } -> { color :: String, size :: Int }
withDefaults given = Record.merge given { color: "red", size: 1 }

names :: forall r. Array { name :: String | r } -> Array String
names = map _.name

totalCount :: forall r. Array { count :: Int | r } -> Int
totalCount = Array.foldl (\acc { count } -> acc + count) 0

main :: Effect Unit
main = do
  let a = { count: 0 }
  let b = { count: 10, name: "b" }
  let c = { count: -1, name: "c", extra: [ 1.5 ], nested: { count: 7 } }
  log (show (bump a) <> show (bump b) <> show (bump c) <> show (bump c.nested))
  log (show (bump' a) <> show (bump' b) <> show (bump' (bump' c)))
  log (show (withId 1 a) <> show (withId 2 b) <> show (withId 3 {}))
  log (show (withDefaults {}) <> show (withDefaults { size: 5 }) <> show (withDefaults { color: "blue", size: 2 }))
  log (show (names [ b, c # Record.delete (Proxy @"extra") # Record.delete (Proxy @"nested") ]) <> show (names [ { name: "solo" } ]))
  log (show (totalCount [ a ]) <> show (totalCount [ b, b ]) <> show (totalCount [ c ]))
  let table = Map.fromFoldable [ "x" /\ b, "y" /\ bump b ]
  log (show (map bump table) <> show (Map.lookup "y" table <#> _.count))
  log (show ([ c, bump c ] <#> _.nested.count) <> show (([ c ] <#> _ { nested { count = 0 } }) == [ c { nested = { count: 0 } } ]))
  log (show (Array.sortWith _.count [ bump c, c, c { count = 100 } ]))
  let polyBumpAll :: forall r. Array { count :: Int | r } -> Array { count :: Int | r }
      polyBumpAll = map bump
  log (show (polyBumpAll [ a ]) <> show (polyBumpAll [ b ]))
