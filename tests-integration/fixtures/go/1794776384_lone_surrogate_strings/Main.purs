module Main where

import Prelude

import Data.String.CodeUnits as CU

-- A literal holding a lone surrogate is spelled in WTF-8.
lone :: String
lone = "a\xD835"

-- Appending two strings that may meet in a lone surrogate on each side joins them through
-- prim.Append or prim.Concat; a non-empty constant between them keeps Go's own `+`.
halves :: String -> String -> String
halves high low = high <> low

chain :: String -> String -> String -> String
chain a b c = a <> b <> c

separated :: String -> String -> String
separated a b = "<" <> a <> ", " <> b <> ">"

isAstral :: String -> Boolean
isAstral s = case s of
  "\xD835" -> false
  _ -> CU.length s == 2

main :: Array String
main =
  [ halves (CU.drop 1 lone) (CU.drop 1 "\x1D400")
  , chain lone "" (CU.drop 1 "\x1D400")
  , separated lone lone
  , show (isAstral (CU.take 1 "\x1D400"))
  ]
