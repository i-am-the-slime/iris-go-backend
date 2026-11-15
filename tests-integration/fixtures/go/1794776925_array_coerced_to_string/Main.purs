module Main where

import Prelude

import Unsafe.Coerce (unsafeCoerce)

-- JavaScript turns an array that meets a string into its elements joined with commas.
main :: String
main = "letters: " <> unsafeCoerce [ "a", "b", "c" ] <> "; nested: " <> unsafeCoerce [ [ "d", "e" ], [ "f" ] ]
