module Main where

check :: { name :: String, age :: Int } -> String
check rec = rec.
--              ^

check2 :: { name :: String, age :: Int } -> String
check2 rec = rec.
--               #
