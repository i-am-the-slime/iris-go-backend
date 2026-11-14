module Bench.String.CharAtAscii where

import Prelude

import Bench.Harness (benchmark)
import Bench.Text as Text
import Data.Maybe (Maybe(..))
import Data.String.CodeUnits as CodeUnits
import Data.String.Pattern (Pattern(..))
import Effect (Effect)

hypothesis :: String
hypothesis = "charAt i, indexOf' from an offset and length in the loop condition are O(1) in JS; Go walks the UTF-8 prefix to find code unit i"

main :: Effect Unit
main = benchmark { size: 16000, workload }

workload :: Int -> String
workload n = do
  let text = Text.ascii n
  show (vowels text) <> " " <> show (occurrences text) <> " " <> show (chunks text)
  where
  vowels text = countVowels 0 0
    where
    countVowels i count
      | i >= CodeUnits.length text = count
      | otherwise = countVowels (i + 1) (if isVowel (CodeUnits.charAt i text) then count + 1 else count)

  occurrences text = countFrom 0 0
    where
    countFrom offset count = case CodeUnits.indexOf' (Pattern "o") offset text of
      Just found -> countFrom (found + 1) (count + 1)
      Nothing -> count

  chunks text = countChunks text 0
    where
    countChunks rest count
      | CodeUnits.length rest == 0 = count
      | otherwise = countChunks (CodeUnits.drop 7 rest) (count + CodeUnits.length (CodeUnits.take 7 rest))

  isVowel = case _ of
    Just 'a' -> true
    Just 'e' -> true
    Just 'i' -> true
    Just 'o' -> true
    Just 'u' -> true
    _ -> false
