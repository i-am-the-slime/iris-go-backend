module Main where

nested :: { inner :: { x :: Int, y :: Int } } -> Int
nested rec = rec.inner.
--                     #
