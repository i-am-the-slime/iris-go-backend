-- | Renders fuzz results as plain ASCII, so that Go and JS outputs compare line by line and a
-- | lone surrogate shows as its own `\uD83D` escape instead of being lost in console encoding.
module Fuzz.Render
  ( run
  , s
  , ms
  , i
  , mi
  , n
  , mn
  , c
  , mc
  , b
  , as
  , ai
  , an
  , ac
  , o
  , ch
  ) where

import Prelude

import Data.Array as Array
import Data.Enum (fromEnum, toEnum)
import Data.Foldable (intercalate, traverse_)
import Data.Int as Int
import Data.Maybe (Maybe, fromJust, maybe)
import Partial.Unsafe (unsafePartial)
import Data.String.CodeUnits as CodeUnits
import Effect (Effect)
import Effect.Console (log)

-- | Prints every case as `label<TAB>result`.
run :: Array { label :: String, result :: Unit -> String } -> Effect Unit
run = traverse_ \{ label, result } -> log (label <> "\t" <> result unit)

s :: String -> String
s text = "\"" <> intercalate "" (map unit' (CodeUnits.toCharArray text)) <> "\""
  where
  unit' char = escape (fromEnum char)
  escape code
    | code >= 0x20 && code < 0x7f && code /= 0x5c && code /= 0x22 = maybe "?" CodeUnits.singleton (toEnum code)
    | otherwise = "\\u" <> pad (Int.toStringAs Int.hexadecimal code)
  pad hex = Array.fold (Array.replicate (4 - CodeUnits.length hex) "0") <> hex

ms :: Maybe String -> String
ms = maybe "Nothing" (\x -> "(Just " <> s x <> ")")

i :: Int -> String
i = show

mi :: Maybe Int -> String
mi = show

n :: Number -> String
n = show

mn :: Maybe Number -> String
mn = show

c :: Char -> String
c char = "'" <> show (fromEnum char) <> "'"

mc :: Maybe Char -> String
mc = maybe "Nothing" (\x -> "(Just " <> c x <> ")")

b :: Boolean -> String
b = show

as :: Array String -> String
as xs = "[" <> intercalate "," (map s xs) <> "]"

ai :: Array Int -> String
ai = show

an :: Array Number -> String
an = show

ac :: Array Char -> String
ac xs = "[" <> intercalate "," (map c xs) <> "]"

o :: Ordering -> String
o = show

-- | The char of a UTF-16 code unit, lone surrogates included.
ch :: Int -> Char
ch code = unsafePartial (fromJust (toEnum code))
