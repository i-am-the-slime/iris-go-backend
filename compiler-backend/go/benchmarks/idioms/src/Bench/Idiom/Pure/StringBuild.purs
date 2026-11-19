module Bench.Idiom.Pure.StringBuild where

import Prelude

import Bench.Harness (benchmark)
import Data.Array as Array
import Data.Char (fromCharCode, toCharCode)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String.CodeUnits as CodeUnits
import Effect (Effect)

idiom :: String
idiom = "string building through Data.String.CodeUnits: fromCharArray over a mapped range, toCharArray and a char map, charAt in a counting go loop"

main :: Effect Unit
main = benchmark { size: 1000000, workload }

workload :: Int -> String
workload n = do
  let rotated = rot13 (build n)
  show (CodeUnits.length rotated) <> " " <> show (vowels rotated) <> " " <> CodeUnits.take 16 rotated

build :: Int -> String
build n = CodeUnits.fromCharArray (map letter (Array.range 0 (n - 1)))
  where
  letter i = fromMaybe 'a' (fromCharCode (97 + i `mod` 26))

rot13 :: String -> String
rot13 text = CodeUnits.fromCharArray (map rotate (CodeUnits.toCharArray text))
  where
  rotate c = do
    let code = toCharCode c
    if code >= 97 && code <= 122 then fromMaybe c (fromCharCode (97 + (code - 97 + 13) `mod` 26)) else c

vowels :: String -> Int
vowels text = go 0 0
  where
  size = CodeUnits.length text

  go i count
    | i >= size = count
    | otherwise = go (i + 1) (if isVowel (CodeUnits.charAt i text) then count + 1 else count)

  isVowel (Just c) = c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u'
  isVowel Nothing = false
