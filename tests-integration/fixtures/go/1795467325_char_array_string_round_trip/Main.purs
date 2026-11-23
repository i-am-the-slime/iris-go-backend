module Main where

import Prelude

import Data.Array as Array
import Data.String.CodeUnits (fromCharArray, toCharArray)

roundTripBuildsNoArray :: String -> String
roundTripBuildsNoArray text = fromCharArray (toCharArray text)

reversedCharsStayAnArray :: String -> String
reversedCharsStayAnArray text = fromCharArray (Array.reverse (toCharArray text))

main :: Array String
main =
  [ roundTripBuildsNoArray "a😀b"
  , reversedCharsStayAnArray "abc"
  ]
