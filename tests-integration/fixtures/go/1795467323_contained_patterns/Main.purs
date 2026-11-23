module Main where

import Prelude

import Data.Maybe (isJust)
import Data.String as String
import Data.String.CodeUnits as CodeUnits
import Data.String.Pattern (Pattern(..))

containsComputesNoIndex :: String -> Boolean
containsComputesNoIndex text = String.contains (Pattern "ab") text

codeUnitContainsComputesNoIndex :: String -> String -> Boolean
codeUnitContainsComputesNoIndex pattern text = CodeUnits.contains (Pattern pattern) text

indexOfStaysAnIndex :: String -> Boolean
indexOfStaysAnIndex text = isJust (String.indexOf (Pattern "ab") text)

main :: Array String
main =
  [ show (containsComputesNoIndex "cab")
  , show (codeUnitContainsComputesNoIndex "😀" "a😀")
  , show (indexOfStaysAnIndex "ba")
  ]
