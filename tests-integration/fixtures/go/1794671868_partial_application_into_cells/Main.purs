module Main where

import Prelude

newtype Reader = Reader (Int -> Int)

runReader :: Int -> Reader -> Int
runReader environment (Reader f) = f environment

plus :: Int -> Reader -> Int -> Int
plus n reader environment
  | n > 100 = plus (n - 100) reader environment
  | otherwise = runReader environment reader + n * environment

addAll :: Int -> Reader -> Reader
addAll 0 reader = reader
addAll n reader = addAll (n - 1) (Reader (plus n reader))

main :: Int
main = runReader 2 (addAll 4 (Reader \environment -> environment))
