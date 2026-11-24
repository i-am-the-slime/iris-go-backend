module Main where

import Prelude

import Data.Array (filter)

beforeAsciiText :: Array String -> Array String
beforeAsciiText = filter (_ < "w2")

afterBmpTextBelowSurrogates :: Array String -> Array String
afterBmpTextBelowSurrogates = filter ("é" < _)

privateUseTextKeepsCodeUnitOrder :: Array String -> Array String
privateUseTextKeepsCodeUnitOrder = filter (_ < "\xE000")

main :: Array (Array String)
main = do
  let words = [ "w1", "w2", "w3", "", "😀", "\xE000", "é", "z" ]
  [ beforeAsciiText words, afterBmpTextBelowSurrogates words, privateUseTextKeepsCodeUnitOrder words ]
