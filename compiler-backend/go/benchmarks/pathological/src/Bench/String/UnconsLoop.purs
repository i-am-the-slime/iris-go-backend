module Bench.String.UnconsLoop where

import Prelude

import Bench.Harness (benchmark)
import Bench.Text as Text
import Data.Maybe (Maybe(..))
import Data.String as String
import Data.String.CodePoints (codePointFromChar)
import Data.String.CodeUnits as CodeUnits
import Effect (Effect)

hypothesis :: String
hypothesis = "consuming a string with uncons: CodeUnits.uncons and CodePoints.uncons slice in O(1) in JS; Go must find the UTF-16 boundary and may copy"

main :: Effect Unit
main = benchmark { size: 20000, workload }

workload :: Int -> String
workload n = do
  let ascii = Text.ascii n
  let unicode = Text.unicode n
  show (countCodeUnits ascii 0) <> " " <> show (countCodeUnits unicode 0) <> " " <> show (countCodePoints unicode 0) <> " " <> show (countCodePoints ascii 0)
  where
  countCodeUnits text count = case CodeUnits.uncons text of
    Just { head, tail } -> countCodeUnits tail (if head == ' ' then count + 1 else count)
    Nothing -> count

  countCodePoints text count = case String.uncons text of
    Just { head, tail } -> countCodePoints tail (if head == space then count + 1 else count)
    Nothing -> count

  space = codePointFromChar ' '
