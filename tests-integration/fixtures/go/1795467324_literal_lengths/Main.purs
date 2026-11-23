module Main where

import Prelude

import Data.Maybe (Maybe)
import Data.String as String
import Data.String.CodeUnits as CodeUnits
import Data.String.Pattern (Pattern(..))

strippedPrefixSplitsAtALiteralLength :: String -> Maybe String
strippedPrefixSplitsAtALiteralLength text = String.stripPrefix (Pattern "😀a") text

literalCodeUnitLengthIsAConstant :: Int
literalCodeUnitLengthIsAConstant = CodeUnits.length "a😀é"

literalCodePointLengthIsAConstant :: Int
literalCodePointLengthIsAConstant = String.length "a😀é"

main :: Array String
main =
  [ show (strippedPrefixSplitsAtALiteralLength "😀ab")
  , show literalCodeUnitLengthIsAConstant
  , show literalCodePointLengthIsAConstant
  ]
