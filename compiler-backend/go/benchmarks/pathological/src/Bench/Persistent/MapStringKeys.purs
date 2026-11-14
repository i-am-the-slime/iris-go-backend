module Bench.Persistent.MapStringKeys where

import Prelude

import Bench.Harness (benchmark)
import Data.Array ((..))
import Data.Array as Array
import Data.Foldable (foldl)
import Data.Map as Map
import Data.String (joinWith)
import Effect (Effect)

hypothesis :: String
hypothesis = "Data.Map keyed by non-ASCII strings: JS compares UTF-16 code units natively, Go must emulate UTF-16 order over UTF-8 bytes"

main :: Effect Unit
main = benchmark { size: 120000, workload }

workload :: Int -> String
workload n = do
  let final = foldl (\map i -> Map.insert (key i) i map) Map.empty (1 .. n)
  let order = joinWith "|" (Array.take 6 (Array.fromFoldable (Map.keys (Map.filterKeys (\k -> k < "a") final))))
  show (Map.size final) <> " " <> order
  where
  key i = prefix i <> show (i `mod` 40000)
  prefix i = case i `mod` 5 of
    0 -> "ｱ"
    1 -> "😀"
    2 -> "日"
    3 -> "\xFFFF"
    _ -> "Ω"
