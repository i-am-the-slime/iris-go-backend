module T.Str where

import Prelude

import Data.Array as Array
import Data.Int as Int
import Data.Maybe (Maybe(..))
import Data.Number as Number
import Data.String as String
import Data.String.CodePoints as CP
import Data.String.CodeUnits as CU
import Data.String.Common (joinWith, replaceAll, split, toLower, toUpper, trim)
import Data.String.Pattern (Pattern(..), Replacement(..))
import Effect (Effect)
import Effect.Console (log)

samples :: Array String
samples = [ "hello", "  padded\t\n", "Straße", "émoji 😀👍🏽 done", "日本語テキスト", "", "a,b,,c", "ǅ İ ß ﬀ" ]

main :: Effect Unit
main = do
  samples <#> String.length # show # log
  samples <#> CU.length # show # log
  samples <#> toUpper # show # log
  samples <#> toLower # show # log
  samples <#> trim # show # log
  samples <#> CP.toCodePointArray <#> map CP.singleton # show # log
  samples <#> CU.toCharArray <#> Array.length # show # log
  samples <#> CP.codePointAt 6 # show # log
  samples <#> CU.charAt 6 # show # log
  samples <#> String.take 7 # show # log
  samples <#> CU.take 7 # show # log
  samples <#> String.drop 2 # show # log
  samples <#> CP.indexOf (Pattern "o") # show # log
  samples <#> CU.indexOf (Pattern "o") # show # log
  samples <#> CP.lastIndexOf (Pattern "😀") # show # log
  samples <#> split (Pattern ",") # show # log
  samples <#> split (Pattern "") # show # log
  samples <#> replaceAll (Pattern "o") (Replacement "0") # show # log
  samples <#> String.replace (Pattern "o") (Replacement "[o]") # show # log
  samples <#> String.stripPrefix (Pattern "he") # show # log
  samples <#> CU.uncons # show # log
  samples <#> CP.uncons # show # log
  samples <#> CP.splitAt 3 # show # log
  samples <#> CU.splitAt 3 # show # log
  samples <#> String.contains (Pattern "😀") # show # log
  log (joinWith "/" samples)
  log (show (Array.sort samples))
  log (show (samples <#> CU.slice 1 4))
  log (show (CU.fromCharArray [ 'a', 'ß', '日' ]) <> show (CP.fromCodePointArray (CP.toCodePointArray "x😀")))
  log (show (CP.codePointFromChar 'A') <> show (map CP.codePointAt [ 0, 1 ] <#> (_ $ "😀")))
  log (show (String.localeCompare "a" "b") <> show ("😀" < "日") <> show (compare "\xFFFF" "😀"))
  [ "42", "-7", "  3", "3.5", "1e3", "0x1F", "", "+5", "2147483648", "-2147483648", "007" ] <#> Int.fromString # show # log
  [ "42", "-7", "  3", "3.5", "1e3", ".5", "abc", "1.5abc", "Infinity", "-0", "NaN", "1_000" ] <#> Number.fromString # show # log
  [ 0.1, 1.0, -0.0, 1.0e21, 1.0e-7, 123.456, 2.0e-323, 1.7976931348623157e308, 100.0, 1.0e20, 5.0e-324 ] <#> show # show # log
  [ 0.1, -2.5, 3.0 ] <#> (\n -> { n, half: n / 2.0, rounded: Int.round n, floor: Int.floor n }) # show # log
  [ 255, -1, 0 ] <#> Int.toStringAs Int.hexadecimal # show # log
  [ "ff", "-z", "10" ] <#> Int.fromStringAs Int.hexadecimal # show # log
  log (show (Int.toNumber 7 / 2.0) <> show (7 / 2) <> show ((-7) / 2) <> show ((-7) `mod` 2) <> show (Int.quot (-7) 2) <> show (Int.rem (-7) 2))
  log (show (Number.nan == Number.nan) <> show (Number.infinity) <> show (-Number.infinity) <> show (Number.nan))
  log (show (Int.ceil 2.1) <> show (Int.round (-2.5)) <> show (Int.round 2.5) <> show (Int.floor 1.0e20) <> show (Int.fromNumber 3.0) <> show (Int.fromNumber 3.5))
  log (show (CU.singleton 'x' <> show 'y' <> show '\n' <> show "tab\there" <> show "q\"uote" <> show "\x1F600" <> show "\x7F\x80"))
