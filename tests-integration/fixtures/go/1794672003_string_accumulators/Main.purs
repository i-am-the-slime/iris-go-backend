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

chainedInFold :: Int -> String
chainedInFold n = foldl (\acc i -> acc <> show i <> ",") "" (1 .. n)

chainedInLoop :: Int -> String
chainedInLoop n = go 0 ""
  where
  go i acc
    | i >= n = acc
    | otherwise = go (i + 1) (acc <> show i <> ";")

chainedWithLiteralFirst :: Int -> String
chainedWithLiteralFirst n = foldl (\acc i -> acc <> "<" <> show i <> ">") "" (1 .. n)

-- Shared: the step reads the accumulator besides appending to it, so it stays a string.
readInFold :: Int -> String
readInFold n = foldl (\acc i -> if CodeUnits.length acc > 5 then acc else acc <> show i) "" (1 .. n)

readInLoop :: Int -> String
readInLoop n = go 0 ""
  where
  go i acc
    | i >= n = acc
    | otherwise = go (i + 1) (acc <> show (CodeUnits.length acc))

-- Shared: the chain reads the accumulator again, so it stays a string.
chainReadsAcc :: Int -> String
chainReadsAcc n = foldl (\acc _ -> acc <> show (CodeUnits.length acc) <> ",") "" (1 .. n)

-- Prepending stays a string concatenation.
prepended :: Int -> String
prepended n = foldl (\acc i -> show i <> acc) "" (1 .. n)

-- Wrapping prepends as well as appends, so it stays a string concatenation.
wrapped :: Int -> String
wrapped n = foldl (\acc i -> "[" <> acc <> show i <> "]") "" (1 .. n)

main :: Array String
main =
  [ appendedInFold 12
  , appendedInLoop 10
  , show (measuredAtExit 5)
  , chainedInFold 12
  , chainedInLoop 12
  , chainedWithLiteralFirst 5
  , readInFold 10
  , readInLoop 12
  , chainReadsAcc 6
  , prepended 5
  , wrapped 4
  ]
