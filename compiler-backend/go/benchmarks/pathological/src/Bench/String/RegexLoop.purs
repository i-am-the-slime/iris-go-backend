module Bench.String.RegexLoop where

import Prelude

import Bench.Harness (benchmark)
import Bench.Text as Text
import Data.Array ((..))
import Data.Array as Array
import Data.Array.NonEmpty as NonEmptyArray
import Data.Either (fromRight')
import Data.Foldable (foldl)
import Data.Maybe (maybe)
import Data.String.CodeUnits as CodeUnits
import Data.String.Regex (Regex, match, regex, replace, test)
import Data.String.Regex.Flags (RegexFlags, global, noFlags)
import Effect (Effect)
import Partial.Unsafe (unsafeCrashWith)

hypothesis :: String
hypothesis = "regex match, test and replace in a loop: V8 and JSC JIT-compile regexes, Go's RE2 runs an automaton and maps UTF-16 offsets"

main :: Effect Unit
main = benchmark { size: 3000, workload }

workload :: Int -> String
workload n = do
  let lines = map line (1 .. n)
  let matched = foldl (\count text -> count + maybe 0 NonEmptyArray.length (match wordPattern text)) 0 lines
  let tested = Array.length (Array.filter (test digitPattern) lines)
  let replaced = foldl (\count text -> count + CodeUnits.length (replace vowelPattern "_" text)) 0 lines
  show matched <> " " <> show tested <> " " <> show replaced
  where
  line i = Text.ascii (i `mod` 40) <> " " <> show i <> " " <> Text.unicode (i `mod` 13)
  wordPattern = compile "[a-z]+" global
  digitPattern = compile "[0-9]{3}" noFlags
  vowelPattern = compile "[aeiouの]" global

compile :: String -> RegexFlags -> Regex
compile source flags = fromRight' (\_ -> unsafeCrashWith source) (regex source flags)
