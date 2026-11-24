module T.Exist where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested (type (/\), (/\))
import Effect (Effect)
import Effect.Console (log)

-- existential via rank-2 CPS
newtype Showable = Showable (forall r. (forall a. Show a => a -> r) -> r)

mkShowable :: forall a. Show a => a -> Showable
mkShowable a = Showable \k -> k a

showIt :: Showable -> String
showIt (Showable run) = run show

-- record of functions built from instances
type Codec a = { encode :: a -> String, name :: String }

codecFor :: forall @a. Show a => String -> Codec a
codecFor name = { encode: \a -> name <> ":" <> show a, name }

-- class with nullary method
class Default a where
  def :: a

instance Default Int where def = 0
instance Default String where def = "?"
instance Default a => Default (Array a) where def = [ def, def ]
instance (Default a, Default b) => Default (a /\ b) where def = def /\ def
instance Default b => Default (a -> b) where def = const def

-- runtime-driven polymorphic recursion
nestShow :: forall a. Show a => Int -> a -> String
nestShow n a = if n <= 0 then show a else nestShow (n - 1) [ a ]

-- function semigroup/monoid
greeting :: Int -> String
greeting = show <> const "!" <> (\n -> if n > 1 then "s" else "")

main :: Effect Unit
main = do
  let things = [ mkShowable 1, mkShowable "two", mkShowable [ Just 3.5 ], mkShowable { a: 1 /\ 'c' } ]
  things <#> showIt # show # log
  let intCodec = codecFor "int" :: Codec Int
  let strCodec = codecFor @String "str"
  log (intCodec.encode 5 <> strCodec.encode "s" <> (codecFor @(Array Boolean) "arr").encode [ true ])
  log (show (def :: Int) <> (def :: String) <> show (def :: Array (Array Int)) <> show (def :: Int /\ Array String) <> (def :: Int -> String) 9)
  log (nestShow 0 1 <> nestShow 3 1 <> nestShow 5 "x")
  log (greeting 1 <> greeting 2 <> (mempty :: Int -> String) 3)
  log (Array.intercalate "," (map (\f -> f 3) [ show, \n -> show (n * n), mempty ]))
