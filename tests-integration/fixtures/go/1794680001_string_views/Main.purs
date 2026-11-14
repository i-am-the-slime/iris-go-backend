module Main where

import Prelude

import Data.Array ((..))
import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.String as String
import Data.String.CodeUnits as CodeUnits
import Data.String.Pattern (Pattern(..))
import Data.String.Unsafe as Unsafe

charAtLoopViewsTheText :: String -> Int -> Int -> Int
charAtLoopViewsTheText text i count
  | i >= CodeUnits.length text = count
  | otherwise = charAtLoopViewsTheText text (i + 1) (if CodeUnits.charAt i text == Just 'a' then count + 1 else count)

unsafeCharAtLoopViewsTheText :: String -> Int -> String -> String
unsafeCharAtLoopViewsTheText text i reversed
  | i < 0 = reversed
  | otherwise = unsafeCharAtLoopViewsTheText text (i - 1) (reversed <> CodeUnits.singleton (Unsafe.charAt i text))

indexOfLoopViewsTheText :: String -> Int -> Int -> Int
indexOfLoopViewsTheText text offset count = case CodeUnits.indexOf' (Pattern "a") offset text of
  Just found -> indexOfLoopViewsTheText text (found + 1) (count + 1)
  Nothing -> count

lastIndexOfLoopViewsTheText :: String -> Int -> Int -> Int
lastIndexOfLoopViewsTheText text offset count = case CodeUnits.lastIndexOf' (Pattern "a") offset text of
  Just found | found > 0 -> lastIndexOfLoopViewsTheText text (found - 1) (count + 1)
  Just _ -> count + 1
  Nothing -> count

slicesInALoopViewTheText :: String -> Int -> Array String -> Array String
slicesInALoopViewTheText text i pieces
  | i >= CodeUnits.length text = pieces
  | otherwise = slicesInALoopViewTheText text (i + 2) (pieces <> [ CodeUnits.slice i (i + 2) text, CodeUnits.take i text, CodeUnits.drop i text ])

codePointLoopViewsTheText :: String -> Int -> Int -> Int
codePointLoopViewsTheText text i count
  | i >= String.length text = count
  | otherwise = codePointLoopViewsTheText text (i + 1) (if String.codePointAt i text == String.codePointAt 0 (String.take (i + 1) text) then count + 1 else count)

changedTextIsWalkedEachIteration :: String -> Int -> Int
changedTextIsWalkedEachIteration rest count = case CodeUnits.charAt (count `mod` 2) rest of
  Just _ -> changedTextIsWalkedEachIteration (CodeUnits.drop (1 + count `mod` 2) rest) (count + 1)
  Nothing -> count

literalIndexesAloneWalkTheText :: String -> Int -> Int
literalIndexesAloneWalkTheText text count
  | count >= 3 = count
  | otherwise = literalIndexesAloneWalkTheText text (count + CodeUnits.length (CodeUnits.take 2 text))

closureInTheLoopReadsTheView :: String -> Int -> Array (Maybe Char) -> Array (Maybe Char)
closureInTheLoopReadsTheView text i found
  | i >= CodeUnits.length text = found
  | otherwise = closureInTheLoopReadsTheView text (i + 3) (found <> map (\offset -> CodeUnits.charAt (i + offset) text) [ 0, 1 ])

arrayIterationViewsTheText :: String -> Array (Maybe Char)
arrayIterationViewsTheText text = map (\i -> CodeUnits.charAt i text) (0 .. (CodeUnits.length text - 1))

singleCallOutsideALoopWalks :: String -> Int -> Maybe Char
singleCallOutsideALoopWalks text i = CodeUnits.charAt i text

text :: String
text = "naïve 😀 banana 日本 a𝄞a"

main :: Array String
main =
  [ show (charAtLoopViewsTheText text 0 0)
  , unsafeCharAtLoopViewsTheText "ab😀c" 4 ""
  , show (indexOfLoopViewsTheText text 0 0)
  , show (lastIndexOfLoopViewsTheText text 100 0)
  , show (slicesInALoopViewTheText "a😀b𝄞" 0 [])
  , show (codePointLoopViewsTheText text 0 0)
  , show (changedTextIsWalkedEachIteration text 0)
  , show (literalIndexesAloneWalkTheText text 0)
  , show (closureInTheLoopReadsTheView "x😀yz" 0 [])
  , show (arrayIterationViewsTheText (String.joinWith " " [ "a😀", text ]))
  , show (singleCallOutsideALoopWalks text (CodeUnits.length text - 3))
  ]
