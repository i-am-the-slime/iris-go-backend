module Main where

import Prelude

main :: Array (Array Boolean)
main = map (\n -> [ n > 1, n > 2 ]) [ 1, 2, 3 ]
