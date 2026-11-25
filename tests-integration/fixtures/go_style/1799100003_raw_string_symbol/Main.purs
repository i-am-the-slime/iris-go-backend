module Main where

import Prelude

import Effect (Effect)
import Effect.Console (log)
import Type.Proxy (Proxy(..))

class Named :: Symbol -> Constraint
class Named s where
  name :: Proxy s -> String

instance Named "box" where
  name _ = "a box"

instance Named "two\nlines" where
  name _ = "two lines"

main :: Effect Unit
main = do
  log (name (Proxy :: Proxy """box"""))
  log (name (Proxy :: Proxy "box"))
  log (name (Proxy :: Proxy """two
lines"""))
