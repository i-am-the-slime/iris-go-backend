module Main where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.String (Pattern(..))
import Data.String as String
import Data.String.CodePoints (codePointFromChar)
import Data.String.CodeUnits as CodeUnits
import Effect (Effect)
import Effect.Console (log)

main :: Effect Unit
main = do
  log "-- letters counted by charAt, past the end and on surrogates"
  each texts \text -> log (show (lettersByCharAt 'a' text) <> " " <> show (lettersByCharAt '\xE9' text))
  log "-- letters counted by codePointAt, astral ones whole"
  each texts \text -> log (show (lettersByCodePointAt 'a' text) <> " " <> show (astralByCodePointAt text))
  log "-- letters counted by uncons, by code point and by code unit"
  each texts \text -> log (show (unconsCodePoints 0 text) <> " " <> show (unconsCodeUnits 0 text) <> " " <> show (surrogatesByUncons 0 text))
  log "-- slices that start with ab"
  each texts \text -> log (show (sliceStarts text))
  log "-- words with a prefix stripped"
  log (show (Array.mapMaybe (String.stripPrefix (Pattern "a")) words))
  log (show (Array.length (Array.mapMaybe (String.stripPrefix (Pattern "\xE9")) words)))
  log (show (map CodeUnits.length (Array.mapMaybe (String.stripPrefix (Pattern "\xD83D")) words)))
  log "-- an array walked from its end by last and init"
  log (show (sumByLastInit 0 [ 1, 2, 3, 4, 5 ]))
  log (show (sumByLastInit 0 []))
  log (show (lastTwo [ 7, 8, 9 ]) <> " " <> show (lastTwo [ 7 ]) <> " " <> show (lastTwo []))
  where
  each :: forall a. Array a -> (a -> Effect Unit) -> Effect Unit
  each values act = void (Array.foldM (\_ value -> act value) unit values)
  texts = [ "", "a", "banana bandana", "\xE9t\xE9 a", "a\x1F600za\x1F600", "\xD83D a\xDE00", "ab\xD83D", "ab ab ab" ]
  words = [ "apple", "", "a", "banana", "\xE9t\xE9", "\x1F600x", "\xD83Dz", "\xE9" ]

lettersByCharAt :: Char -> String -> Int
lettersByCharAt letter text = Array.length (Array.filter (_ == Just letter) (Array.range 0 (CodeUnits.length text) <#> \position -> CodeUnits.charAt position text))

lettersByCodePointAt :: Char -> String -> Int
lettersByCodePointAt letter text = Array.length (Array.filter isLetter (Array.range (-1) (String.length text)))
  where
  isLetter position = String.codePointAt position text == Just (codePointFromChar letter)

astralByCodePointAt :: String -> Int
astralByCodePointAt text = Array.length (Array.filter isAstral (Array.range 0 (String.length text - 1)))
  where
  isAstral position = case String.codePointAt position text of
    Just point -> point > codePointFromChar '\xFFFF'
    Nothing -> false

unconsCodePoints :: Int -> String -> Int
unconsCodePoints found remaining = case String.uncons remaining of
  Just { head, tail } -> unconsCodePoints (if head == codePointFromChar 'a' then found + 1 else found) tail
  Nothing -> found

surrogatesByUncons :: Int -> String -> Int
surrogatesByUncons found remaining = case String.uncons remaining of
  Just { head, tail } -> surrogatesByUncons (if head > codePointFromChar '\xD7FF' then found + 1 else found) tail
  Nothing -> found

unconsCodeUnits :: Int -> String -> Int
unconsCodeUnits found remaining = case CodeUnits.uncons remaining of
  Just { head, tail } -> unconsCodeUnits (if head == 'a' then found + 1 else found) tail
  Nothing -> found

sliceStarts :: String -> Int
sliceStarts text = Array.length (Array.filter startsWithAb (Array.range 0 (CodeUnits.length text / 3)))
  where
  startsWithAb third = CodeUnits.slice (third * 3) (third * 3 + 2) text == "ab"

sumByLastInit :: Int -> Array Int -> Int
sumByLastInit total remaining = case Array.last remaining, Array.init remaining of
  Just final, Just rest -> sumByLastInit (total + final) rest
  _, _ -> total

lastTwo :: Array Int -> String
lastTwo values = case Array.last values, Array.init values >>= Array.last of
  Just final, Just before -> show before <> "," <> show final
  Just final, Nothing -> "only " <> show final
  Nothing, _ -> "none"
