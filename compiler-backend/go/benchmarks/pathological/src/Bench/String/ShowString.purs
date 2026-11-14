module Bench.String.ShowString where

import Prelude

import Bench.Harness (benchmark)
import Bench.Text as Text
import Data.Array ((..))
import Data.Foldable (foldl)
import Data.String.CodeUnits as CodeUnits
import Effect (Effect)

hypothesis :: String
hypothesis = "show on strings escapes per UTF-16 code unit; JS does it with a native JSON-style routine"

main :: Effect Unit
main = benchmark { size: 3000, workload }

workload :: Int -> String
workload n = do
  let texts = map (\i -> Text.unicode (i `mod` 50) <> "\"\n\t\x7f" <> Text.ascii (i `mod` 30)) (1 .. n)
  let shown = foldl (\total text -> total + CodeUnits.length (show text)) 0 texts
  show shown <> " " <> show (Text.unicode 3 <> "\x1\"")
