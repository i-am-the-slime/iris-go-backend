module TL.Vta where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.Symbol (class IsSymbol, reflectSymbol)
import Effect (Effect)
import Effect.Console (log)
import Type.Proxy (Proxy(..))

class Convert a b where
  convert :: a -> b

instance Convert Int String where
  convert = show

instance Convert Int Number where
  convert n = if n > 0 then 1.5 else 0.0

instance Convert String Int where
  convert = const 7

reflectThing :: forall @s. IsSymbol s => String
reflectThing = reflectSymbol (Proxy @s)

pairOf :: forall @a @b. Show a => Show b => a -> b -> String
pairOf a b = show a <> "/" <> show b

emptyOf :: forall @a. Monoid a => a
emptyOf = mempty

recordOf :: forall @s. IsSymbol s => { name :: String, len :: Int }
recordOf = { name: reflectSymbol (Proxy @s), len: 1 }

main :: Effect Unit
main = do
  log (convert @Int @String 5)
  log (show (convert @Int @Number 5))
  log (show (convert @String @Int "x"))
  log (pairOf @Int @String 1 "s")
  log (pairOf @_ @Boolean 2.5 true)
  log (show [ reflectThing @"a", reflectThing @"b" ])
  log (show { first: reflectThing @"x", second: emptyOf @String })
  log (if true then reflectThing @"then" else reflectThing @"else")
  log (case reflectThing @"scrutinee" of
    "scrutinee" -> "matched"
    _ -> "nope")
  log (show (Array.length (emptyOf @(Array Int))))
  log (show ([ 1, 2 ] <#> const (reflectThing @"mapped")))
  log (show (emptyOf @(Array String) <> [ "z" ]))
  log (show (recordOf @"abc" == { name: "abc", len: 1 }))
  log (show (recordOf @"abc"))
  log (show ((recordOf @"abcd").len + 1))
  log ((recordOf @"chained").name)
  log (show (map _.name [ recordOf @"m1", recordOf @"m2" ]))
  log (show (Just (recordOf @"in Just") <#> _.name))
