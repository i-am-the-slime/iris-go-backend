module Bench.String.CodePointIndex where

import Prelude

import Bench.Harness (benchmark)
import Bench.Text as Text
import Data.Maybe (Maybe(..))
import Data.String as String
import Data.String.CodePoints (codePointFromChar)
import Effect (Effect)

hypothesis :: String
hypothesis = "Data.String codePointAt i, take, drop and splitAt by code point re-walk the prefix in both runtimes, but Go also re-decodes UTF-8 and allocates arrays"

main :: Effect Unit
main = benchmark { size: 1500, workload }

workload :: Int -> String
workload n = do
  let text = Text.unicode n
  show (spaces text) <> " " <> show (pieces text) <> " " <> String.take 12 text
  where
  spaces text = countSpaces 0 0
    where
    countSpaces i count
      | i >= String.length text = count
      | otherwise = countSpaces (i + 1) (if String.codePointAt i text == Just space then count + 1 else count)

  pieces text = countPieces text 0
    where
    countPieces rest count
      | String.null rest = count
      | otherwise = do
          let { before, after } = String.splitAt 5 rest
          countPieces (String.drop 0 after) (count + String.length before)

  space = codePointFromChar ' '
