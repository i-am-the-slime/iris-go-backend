module Main where

import Prelude

import Native as Native
import Native.Graphics as Graphics

render :: Int -> String
render size = Native.label size <> Graphics.draw size

report :: Int -> String
report size = render size <> Native.label (size + 1)

main :: Array String
main = [ report 1, Native.version ]
