module Main where

import Prelude

import Data.String.CodeUnits (fromCharArray, toCharArray)

shout :: String -> String
shout text = fromCharArray (map upper (toCharArray text))
  where
  upper c = if c == 'a' then 'A' else c

-- | The chars of a string built from chars are those chars: `toCharArray (fromCharArray cs)` is
-- | `cs`, with no string built in between, so the two maps run as one loop over `cs`.
rebuilt :: Array Char -> String
rebuilt chars = shout (fromCharArray (map (\c -> if c == 'b' then 'a' else c) chars))

main :: Array String
main = [ rebuilt [ 'a', 'b', 'c' ], rebuilt [ 'é', 'b' ], shout "banana" ]
