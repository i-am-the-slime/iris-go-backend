module Main where

import Prelude

import Data.Maybe (Maybe(..))
import Data.String as String
import Data.String.CodePoints (codePointFromChar)
import Data.String.CodeUnits as CodeUnits

countSpacesUnconsingCountsUpToTwo :: String -> Int -> Int
countSpacesUnconsingCountsUpToTwo text count = case String.uncons text of
  Just { head, tail } -> countSpacesUnconsingCountsUpToTwo tail (if head == codePointFromChar ' ' then count + 1 else count)
  Nothing -> count

switchedLengthCountsUpToThree :: String -> String
switchedLengthCountsUpToThree text = case CodeUnits.length text of
  0 -> "empty"
  1 -> "one"
  2 -> "two"
  _ -> "many"

comparedCodePointLengthCountsUpToFive :: String -> Boolean
comparedCodePointLengthCountsUpToFive text = String.length text < 4

codePointLengthBuildsNoArray :: String -> Int
codePointLengthBuildsNoArray text = String.length text

unchangedTextLengthIsCountedBeforeTheLoop :: String -> Int -> Int -> Int
unchangedTextLengthIsCountedBeforeTheLoop text i count
  | i >= CodeUnits.length text = count
  | otherwise = unchangedTextLengthIsCountedBeforeTheLoop text (i + 1) (if CodeUnits.charAt i text == Just 'a' then count + 1 else count)

changedRestLengthIsCountedEachIteration :: String -> Int -> Int
changedRestLengthIsCountedEachIteration rest count
  | CodeUnits.length rest < 3 = count
  | otherwise = changedRestLengthIsCountedEachIteration (CodeUnits.drop (CodeUnits.length rest / 2) rest) (count + 1)

main :: Array String
main =
  [ show (countSpacesUnconsingCountsUpToTwo "a b c" 0)
  , switchedLengthCountsUpToThree "ab"
  , show (comparedCodePointLengthCountsUpToFive "word")
  , show (codePointLengthBuildsNoArray "a😀")
  , show (unchangedTextLengthIsCountedBeforeTheLoop "banana" 0 0)
  , show (changedRestLengthIsCountedEachIteration "abcdefghij" 0)
  ]
