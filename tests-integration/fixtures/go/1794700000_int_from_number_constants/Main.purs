module Main where

import Prelude

import Data.Int (fromNumber)
import Data.Maybe (Maybe)

opaque :: Number -> Number
opaque x = if x == 12345.0 then opaque x else x

main :: Array (Maybe Int)
main =
  [ fromNumber 3.0e10
  , fromNumber (-3.0e10)
  , fromNumber 2147483647.0
  , fromNumber (-2147483648.0)
  , fromNumber 2.5
  , fromNumber (-0.0)
  , fromNumber (opaque 3.0e10)
  ]
