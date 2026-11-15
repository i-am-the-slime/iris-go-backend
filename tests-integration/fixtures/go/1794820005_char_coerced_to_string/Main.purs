module Main where

import Prelude

import Data.Array.NonEmpty as NonEmptyArray
import Data.String.NonEmpty as NonEmptyString
import Data.String.NonEmpty.CodeUnits as NonEmptyCodeUnits

main :: String
main = NonEmptyString.toString (NonEmptyCodeUnits.fromFoldable1 (NonEmptyArray.cons' 'a' [ 'b', 'c' ]))
