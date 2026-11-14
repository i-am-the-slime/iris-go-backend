module Main where

import Prelude

import Data.Array ((..))
import Data.Foldable (foldl)
import Data.String.CodeUnits as CodeUnits

appendedInFold :: Int -> String
appendedInFold n = foldl (\acc i -> acc <> show i) "start:" (1 .. n)

appendedInLoop :: Int -> String
appendedInLoop n = go 0 ""
  where
  go i acc
    | i >= n = acc
    | i `mod` 3 == 0 = go (i + 1) acc
    | otherwise = go (i + 1) (acc <> "é")

-- The loop's exit reads the string once it is complete.
measuredAtExit :: Int -> Int
measuredAtExit n = go 0 "x"
  where
  go i acc
    | i >= n = CodeUnits.length acc
    | otherwise = go (i + 1) (acc <> "yz")

-- Shared: the step reads the accumulator besides appending to it, so it stays a string.
readInFold :: Int -> String
readInFold n = foldl (\acc i -> if CodeUnits.length acc > 5 then acc else acc <> show i) "" (1 .. n)

readInLoop :: Int -> String
readInLoop n = go 0 ""
  where
  go i acc
    | i >= n = acc
    | otherwise = go (i + 1) (acc <> show (CodeUnits.length acc))

-- Prepending stays a string concatenation.
prepended :: Int -> String
prepended n = foldl (\acc i -> show i <> acc) "" (1 .. n)

main :: { fold :: String, loop :: String, exit :: Int, readInFold :: String, readInLoop :: String, prepended :: String }
main =
  { fold: appendedInFold 12
  , loop: appendedInLoop 10
  , exit: measuredAtExit 5
  , readInFold: readInFold 10
  , readInLoop: readInLoop 12
  , prepended: prepended 5
  }
