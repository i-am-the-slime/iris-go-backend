module Main where

import Prelude

import Data.Tuple.Nested ((/\))
import Foreign.Object (Object)
import Foreign.Object as Object
import Yoga.JSON (writeJSON)

scores :: Object Int
scores = Object.fromFoldable [ "b" /\ 1, "10" /\ 2, "2" /\ 3 ]

main :: Array String
main = [ writeJSON scores, show (Object.keys scores) ]
