module Main where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.String as String
import Data.String.CodeUnits as CodeUnits
import Data.String.Pattern (Pattern(..))
import Effect (Effect)
import Effect.Console (log)

main :: Effect Unit
main = do
  log "-- code units unconsed one at a time, surrogates and all"
  log (show (texts <#> codeUnitsOf))
  log (show (texts <#> countUnitA 0))
  log "-- code points unconsed one at a time, a lone surrogate on its own"
  log (show (texts <#> codePointsOf))
  log "-- two code units at a time"
  log (show (texts <#> pairsOf))
  log "-- prefixes stripped, a lone surrogate split off a pair"
  log (show (Array.mapMaybe (String.stripPrefix (Pattern "a")) texts))
  log (show (Array.mapMaybe (String.stripPrefix (Pattern "ab")) texts))
  log (show (Array.mapMaybe (String.stripPrefix (Pattern "\xD83D")) texts))
  log (show (texts <#> \text -> CodeUnits.splitAt 1 text))
  log "-- every third pair of code units sliced out of the whole text"
  log (show (texts <#> slicedPairs))
  log (show (texts <#> countAbSlices))
  log (show (texts <#> \text -> Array.range (-3) 3 <#> \from -> CodeUnits.slice from (from + 2) text))
  log "-- every code unit and code point read by its index"
  log (show (texts <#> unitsByIndex))
  log (show (texts <#> pointsByIndex))
  where
  texts = [ "", "a", "ab", "abc", "\xE9", "a\xE9 b", "\x1F600", "a\x1F600 b", "\xD83D", "\xDE00 a", "a\xD83D b", "\xD83D\xD83D", "\xDE00\xDE00", "aab\x1F600 ab\xD83D ab" ]

codeUnitsOf :: String -> Array Char
codeUnitsOf = go []
  where
  go found remaining = case CodeUnits.uncons remaining of
    Just { head, tail } -> go (Array.snoc found head) tail
    Nothing -> found

countUnitA :: Int -> String -> Int
countUnitA found remaining = case CodeUnits.uncons remaining of
  Just { head, tail } -> countUnitA (if head == 'a' then found + 1 else found) tail
  Nothing -> found

codePointsOf :: String -> Array String
codePointsOf = go []
  where
  go found remaining = case String.uncons remaining of
    Just { head, tail } -> go (Array.snoc found (show head)) tail
    Nothing -> found

pairsOf :: String -> Array String
pairsOf = go []
  where
  go found remaining
    | CodeUnits.length remaining == 0 = found
    | otherwise = go (Array.snoc found (CodeUnits.take 2 remaining)) (CodeUnits.drop 2 remaining)

slicedPairs :: String -> Array String
slicedPairs text = Array.range 0 (CodeUnits.length text / 3) <#> \third -> CodeUnits.slice (third * 3) (third * 3 + 2) text

countAbSlices :: String -> Int
countAbSlices text = Array.length (Array.filter startsWithAb (Array.range 0 (CodeUnits.length text / 3)))
  where
  startsWithAb third = CodeUnits.slice (third * 3 - 1) (third * 3 + 1) text == "ab"

unitsByIndex :: String -> Array (Maybe Char)
unitsByIndex text = Array.range 0 (CodeUnits.length text) <#> \position -> CodeUnits.charAt position text

pointsByIndex :: String -> Array (Maybe String)
pointsByIndex text = Array.range (-1) (String.length text) <#> \position -> show <$> String.codePointAt position text
