module Main where

foo x = x

bar = foo 1
--    *

baz = foo (foo 2)
--    *
