module Fun.Strings where

import Prelude

import Data.Array ((..))
import Data.Either (either)
import Data.Enum (enumFromTo, fromEnum)
import Data.Foldable (for_)
import Data.Tuple.Nested ((/\))
import Data.Int as Int
import Data.Maybe (Maybe(..))
import Data.Number as Number
import Data.String as String
import Data.String.CodeUnits as CodeUnits
import Data.String.CodePoints as CodePoints
import Data.String.Pattern (Pattern(..), Replacement(..))
import Data.String.Regex as Regex
import Data.String.Regex.Flags (global, ignoreCase, noFlags, multiline, unicode)
import Effect (Effect)
import Effect.Console (log)

main :: Effect Unit
main = do
  let emoji = "a😀b"
  log $ show (CodeUnits.length emoji) <> " " <> show (CodePoints.length emoji)
  log $ show (CodeUnits.toCharArray emoji)
  log $ show (CodeUnits.charAt 1 emoji) <> show (CodeUnits.charAt 2 emoji) <> show (CodeUnits.charAt 3 emoji)
  log $ show (CodeUnits.take 2 emoji) <> show (CodeUnits.drop 2 emoji)
  log $ (CodeUnits.take 2 emoji <> CodeUnits.drop 2 emoji)
  log $ show (CodeUnits.indexOf (Pattern "b") emoji) <> show (CodePoints.indexOf (Pattern "b") emoji)
  log $ show (CodeUnits.slice 1 3 emoji == "😀")
  log $ show (CodeUnits.splitAt 2 emoji)
  log $ show (CodePoints.splitAt 2 emoji)
  log $ show (CodeUnits.fromCharArray (CodeUnits.toCharArray emoji) == emoji)
  log $ show (String.toCodePointArray "é😀" <#> fromEnum)
  log $ show (CodeUnits.lastIndexOf (Pattern "a") "banana") <> show (CodeUnits.indexOf' (Pattern "a") 2 "banana")
  log $ show (String.split (Pattern ",") "a,b,,c,") <> show (String.split (Pattern "") "abc") <> show (String.split (Pattern "") "a😀")
  log $ show (String.replace (Pattern "a") (Replacement "o") "banana")
  log $ show (String.replaceAll (Pattern "") (Replacement "-") "abc")
  log $ show (String.trim "  \t padded \n ") <> show (String.trim "\x00a0x\x2003")
  log $ show (String.stripPrefix (Pattern "ab") "abc") <> show (String.stripSuffix (Pattern "bc") "abc")
  log $ show (String.contains (Pattern "") "x") <> show (String.null "") <> show (String.localeCompare "a" "B")
  log $ show (CodeUnits.uncons "") <> show (CodeUnits.uncons "😀x")
  log $ show (CodePoints.uncons "😀x")
  log $ show (CodeUnits.dropWhile (_ == 'a') "aab") <> show (CodePoints.takeWhile (\c -> c /= String.codePointFromChar 'b') "a😀b")
  log $ show (enumFromTo 'a' 'e' :: Array Char) <> show (top :: Char) <> show (bottom :: Char)
  log "-- int parsing"
  for_ [ "12", " 12", "12 ", "+5", "-0", "0x10", "1e3", "2147483647", "2147483648", "-2147483648", "-2147483649", "", "1.0", "007", "１２" ] \text ->
    log (show text <> " -> " <> show (Int.fromString text))
  log "-- number parsing"
  for_ [ "1.5", " 1.5 ", "1e3", "1E-2", ".5", "5.", "Infinity", "-Infinity", "NaN", "0x10", "1.5abc", "abc", "", "+2", "1_000", "-0", "1e400" ] \text ->
    log (show text <> " -> " <> show (Number.fromString text))
  log "-- number functions"
  log $ show (5.5 `mod` 2.0) <> " " <> show (5.5 / 2.0) <> " " <> show (Number.remainder 5.5 2.0) <> " " <> show ((-5.5) `Number.remainder` 2.0)
  log $ show (Number.pow 2.0 0.5) <> " " <> show (Number.atan2 1.0 (-1.0)) <> " " <> show (Number.exp 1.0) <> " " <> show (Number.log 10.0)
  log $ show (Number.sin 1.0) <> " " <> show (Number.cos 1.0) <> " " <> " " <>show (Number.round (-2.5)) <> " " <> show (Number.round 2.5)
  log $ show (Number.trunc (-2.7)) <> show (Number.floor (-0.5)) <> show (Number.ceil (-0.5)) <> show (Number.sign (-3.0)) <> show (Number.abs (-0.0))
  log $ show (Number.isFinite (1.0 / 0.0)) <> show (Number.isNaN (0.0 / 0.0)) <> show (Number.min 1.0 2.0)
  log $ show (Int.toNumber 3 / 0.0) <> show (Int.ceil 2.000001) <> show (Int.round 0.49999999999999994)
  log $ show (Int.toStringAs Int.decimal (-0)) <> show (Int.even (-3)) <> show (Int.odd (-3)) <> show (Int.parity 4 == Int.Even)
  log "-- regex"
  let regexes = [ "a+" /\ global, "(\\w+)@(\\w+)" /\ noFlags, "^b" /\ multiline, "B" /\ ignoreCase, "." /\ unicode, "(?<year>\\d{4})" /\ noFlags, "a(?=b)" /\ global, "(a)\\1" /\ noFlags ]
  for_ regexes \(source /\ flags) -> case Regex.regex source flags of
    _ -> log (source <> " " <> either identity (\re -> show (Regex.test re "aab abb\nbob ann@mail 2024 😀")) (Regex.regex source flags))
  let wordRegex = Regex.regex "(\\w+)@(\\w+)" global
  for_ wordRegex \re -> do
    log $ show (Regex.match re "x@y and p@q")
    log $ Regex.replace re "$2 at $1" "x@y and p@q"
    log $ show (Regex.split re "1 x@y 2 p@q 3")
    log $ show (Regex.search re "  x@y")
  for_ (Regex.regex "(o)(x)?" noFlags) \re -> log (show (Regex.match re "foo"))
  for_ (Regex.regex "a|" global) \re -> log (Regex.replace re "-" "banana")
  for_ (Regex.regex "\\s+" global) \re -> log (show (Regex.split re " a  b\tc "))
  for_ (Regex.regex "😀" global) \re -> log (Regex.replace re "x" "a😀b😀")
  where
  _ = 1 .. 2
