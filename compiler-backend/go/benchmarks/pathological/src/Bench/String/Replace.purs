module Bench.String.Replace where

import Prelude

import Bench.Text as Text
import Bench.Harness (benchmark)
import Data.Array ((..))
import Data.Foldable (foldl)
import Data.String (Pattern(..), Replacement(..), replaceAll)
import Data.String.CodeUnits as CodeUnits
import Effect (Effect)

hypothesis :: String
hypothesis = "replaceAll over the same medium string repeatedly: JS uses a native split/join, Go strings.ReplaceAll is fine unless the helper converts to UTF-16"

main :: Effect Unit
main = benchmark { size: 400, workload }

workload :: Int -> String
workload n = do
  let asciiText = Text.ascii 2000
  let unicodeText = Text.unicode 2000
  let total = foldl (\count i -> count + step asciiText i + step unicodeText i) 0 (1 .. n)
  show total
  where
  step text i = CodeUnits.length (replaceAll (Pattern "o") (Replacement (show (i `mod` 7))) (replaceAll (Pattern "の") (Replacement "no") text))
