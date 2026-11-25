module Main where

import Type.Proxy (Proxy(..))

class Named :: Symbol -> Constraint
class Named s where
  name :: Proxy s -> String

instance Named "box" where
  name _ = "a box"

rawName :: String
rawName = name (Proxy :: Proxy """box""")

rawAsPlain :: Proxy "box"
rawAsPlain = Proxy :: Proxy """box"""

plainAsRaw :: Proxy """box"""
plainAsRaw = Proxy :: Proxy "box"

multilineAsEscaped :: Proxy "two\nlines"
multilineAsEscaped = Proxy :: Proxy """two
lines"""
