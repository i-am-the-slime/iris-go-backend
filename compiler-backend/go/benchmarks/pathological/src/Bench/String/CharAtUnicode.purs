module Bench.String.CharAtUnicode where

import Prelude

import Bench.Harness (benchmark)
import Bench.Text as Text
import Data.Maybe (Maybe(..))
import Data.String.CodeUnits as CodeUnits
import Data.String.Pattern (Pattern(..))
import Effect (Effect)

hypothesis :: String
hypothesis = "the same UTF-16 code unit loop over CJK and emoji text, where Go cannot take an ASCII shortcut"

main :: Effect Unit
main = benchmark { size: 12000, workload }

workload :: Int -> String
workload n = do
  let text = Text.unicode n
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
