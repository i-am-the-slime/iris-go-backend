module Main where

import Prelude

import Checks (checked)
import Effect (Effect)
import Journal (log)

main :: Effect Unit
main = log (show (checked [5, -3, 200]))
