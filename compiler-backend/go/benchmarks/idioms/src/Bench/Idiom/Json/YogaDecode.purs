module Bench.Idiom.Json.YogaDecode where

import Prelude

import Bench.Harness (benchmark)
import Bench.Idiom.Json.Document (Document, checksum, document)
import Data.Array as Array
import Data.Either (either)
import Data.Foldable (sum)
import Data.String.CodeUnits as CodeUnits
import Effect (Effect)
import Yoga.JSON (readJSON, writeJSON)

idiom :: String
idiom = "Yoga.JSON readJSON of a 1.1 MB document of nested records, arrays, strings, numbers and Maybe, repeated"

main :: Effect Unit
main = benchmark { size: 8, workload }

workload :: Int -> String
workload n = show (CodeUnits.length input) <> " " <> show (sum (map decode (Array.range 1 n)))
  where
  decode i = either (const (-i)) checksum (readJSON (inputFor i) :: _ _ Document)
  -- The input depends on the iteration so that no decode is shared between iterations.
  inputFor i = if i == 0 then "" else input

input :: String
input = writeJSON (document 10000)
