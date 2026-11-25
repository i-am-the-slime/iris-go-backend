module Main where

import Prelude

import Type.Proxy (Proxy(..))

class Named :: Symbol -> Constraint
class Named s where
  name :: Proxy s -> String

instance Named "box" where
  name _ = "a box"

main :: Array String
main = [ name (Proxy :: Proxy """box"""), name (Proxy :: Proxy "box") ]
