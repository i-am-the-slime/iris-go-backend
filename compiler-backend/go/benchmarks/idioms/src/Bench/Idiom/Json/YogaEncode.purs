module Bench.Idiom.Json.YogaEncode where

import Prelude

import Bench.Harness (benchmark)
import Bench.Idiom.Json.Document (Document, document)
import Data.Array as Array
import Data.Foldable (sum)
import Data.String.CodeUnits as CodeUnits
import Effect (Effect)
import Yoga.JSON (writeJSON)

idiom :: String
idiom = "Yoga.JSON writeJSON of a 1.1 MB document of nested records, arrays, strings, numbers and Maybe, repeated"

main :: Effect Unit
main = benchmark { size: 8, workload }

workload :: Int -> String
workload n = show (sum (map encode (Array.range 1 n)))
  where
  encode i = CodeUnits.length (writeJSON (doc { version = i })) - i

doc :: Document
doc = document 10000
