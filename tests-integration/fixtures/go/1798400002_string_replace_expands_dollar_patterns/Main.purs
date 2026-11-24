module Main where

import Prelude

import Data.String as String
import Data.String.Pattern (Pattern(..), Replacement(..))

main :: Array String
main =
  [ String.replace (Pattern "an") (Replacement "[$&|$`|$'|$$]") "banana"
  , String.replaceAll (Pattern "an") (Replacement "<$&>") "banana"
  ]
