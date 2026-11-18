module Main where

import Prelude

import Data.Exists (Exists, mkExists, runExists)

data Nest a = Nest a

nested :: Int -> Exists Nest -> Int
nested n e
  | n <= 0 = 0
  | otherwise = runExists (\x -> 1 + nested (n - 1) (mkExists (Nest x))) e

wrap :: forall a. Nest a -> Exists Nest
wrap x = mkExists (Nest x)

nestedApart :: Int -> Exists Nest -> Int
nestedApart n e
  | n <= 0 = 0
  | otherwise = runExists (\x -> 1 + nestedApart (n - 1) (wrap x)) e

main :: Array Int
main = [ nested 3 (mkExists (Nest 1)), nestedApart 4 (mkExists (Nest "deep")) ]
