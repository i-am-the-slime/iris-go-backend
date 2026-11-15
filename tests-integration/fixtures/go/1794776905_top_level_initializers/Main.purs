module Main where

import Prelude

-- A top-level value whose evaluation calls a function is computed by an initializer that reports
-- an exception escaping it, as main does: the program then ends with JS's status 1 while it loads.
total :: Int
total = count 5

count :: Int -> Int
count n = if n <= 0 then 0 else 1 + count (n - 1)

-- One that only builds data stays a plain variable.
names :: Array String
names = [ "a", "b" ]

main :: Array String
main = map (_ <> show total) names
