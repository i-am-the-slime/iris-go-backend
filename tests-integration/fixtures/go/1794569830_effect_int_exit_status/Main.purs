module Main where

import Prelude

import Effect (Effect)

-- An `Effect Int` entry point's result is the program's exit status.
main :: Effect Int
main = pure 3
