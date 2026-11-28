module Main where

import Prelude

import Control.Monad.ST (ST, for, run)
import Data.Array.ST (STArray)
import Data.Array.ST as STArray
import Data.Maybe (fromMaybe)

insertionSort :: forall region. STArray region Int -> ST region Unit
insertionSort array = do
  size <- STArray.length array
  for 1 size \i -> do
    current <- peekOrZero i
    shiftDown current (i - 1)
  where
  peekOrZero i = map (fromMaybe 0) (STArray.peek i array)

  shiftDown current j
    | j < 0 = void (STArray.poke 0 current array)
    | otherwise = do
        previous <- peekOrZero j
        if previous > current then do
          _ <- STArray.poke (j + 1) previous array
          shiftDown current (j - 1)
        else void (STArray.poke (j + 1) current array)

digitSums :: Int -> Int
digitSums n = go n 0
  where
  digitSum x acc
    | x == 0 = acc
    | otherwise = digitSum (x / 10) (acc + x `mod` 10)

  go i acc
    | i == 0 = acc
    | otherwise = go (i - 1) (acc + digitSum i 0)

main :: Array Int
main = [ digitSums 100 ] <> run (STArray.withArray insertionSort [ 3, 1, 2 ])
