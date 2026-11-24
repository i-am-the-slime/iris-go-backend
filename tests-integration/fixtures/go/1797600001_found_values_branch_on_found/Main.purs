module Main where

import Prelude

import Data.Int as Int
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String (Pattern(..))
import Data.String.CodeUnits (charAt, indexOf)
import Foreign.Object as Object

-- | A Maybe that a lookup answers is its value and whether it is there, as Go's own lookups
-- | answer: `first, found := prim.CodeUnitCharAt(0, word)`, then `if !found { first = '?' }`.
firstLetter :: String -> Char
firstLetter word = fromMaybe '?' (charAt 0 word)

-- | Each alternative is a branch on `found`, the `Just` one with the value bound.
position :: String -> String
position text = case indexOf (Pattern "b") text of
  Just at -> "b at " <> show at
  Nothing -> "no b"

prices :: Object.Object Int
prices = Object.fromHomogeneous { apple: 3, pear: 5 }

price :: String -> Int
price fruit = fromMaybe 0 (Object.lookup fruit prices)

-- | `member` asks the same lookup with `false` and `const true` in place of the constructors.
stocked :: String -> Boolean
stocked fruit = Object.member fruit prices

parsed :: String -> Int
parsed text = case Int.fromString text of
  Just number -> number * 2
  Nothing -> -1

-- | A Maybe that is kept, rather than matched at once, is built from the two answers.
letters :: Array String -> Array (Maybe Char)
letters words = map (charAt 1) words

main :: Array String
main =
  [ show (firstLetter "plum")
  , show (firstLetter "")
  , position "abc"
  , position "xyz"
  , show (price "pear")
  , show (price "fig")
  , show (stocked "apple")
  , show (stocked "fig")
  , show (parsed "21")
  , show (parsed "x")
  , show (letters [ "ab", "c" ])
  ]
