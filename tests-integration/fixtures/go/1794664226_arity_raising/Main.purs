module Main where

import Prelude

offset :: Int -> Int -> Int
offset 0 = \x -> x
offset n = \x -> offset (n - 1) x + 1

repeat :: Int -> String
repeat 0 = ""
repeat n = "*" <> repeat (n - 1)

prefixed :: Int -> String -> String
prefixed 0 = \text -> text
prefixed n = let prefix = repeat n in \text -> prefix <> prefixed (n - 1) text

main :: Array String
main =
  map (\shift -> show (shift 1)) [ offset 2, offset 5 ]
    <> [ show (offset 3 4) ]
    <> map (prefixed 2) [ "a", "b" ]
