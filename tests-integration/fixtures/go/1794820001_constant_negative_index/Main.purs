module Main where

import Prelude

import Data.Array ((!!))
import Data.Maybe (Maybe)

numbers :: Array Int
numbers = [ 1, 2, 3 ]

main :: Array (Maybe Int)
main = [ numbers !! (-1), numbers !! 1, [ 4, 5 ] !! (-2) ]
