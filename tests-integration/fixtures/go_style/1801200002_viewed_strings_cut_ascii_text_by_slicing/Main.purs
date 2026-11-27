module Main where

import Prelude

import Control.Alternative (guard)
import Data.Array as Array
import Data.String.CodeUnits (charAt, drop, length, singleton, take)
import Effect (Effect)
import Effect.Console (log)

main :: Effect Unit
main = do
  log "-- every word one letter away, cut where the letter goes"
  log (show (oneLetterAway "hit"))
  log (show (oneLetterAway "a"))
  log (show (oneLetterAway ""))
  log "-- the same cuts of text that is not ASCII, a pair split in the middle"
  log (show (oneLetterAway "h\x1F600t"))
  log (show (oneLetterAway "\xE9t\xE9"))
  log "-- cuts before the start and past the end"
  log (show (cuts "word"))
  log (show (cuts "w\x1F600rd"))
  log (show (cuts ""))
  where
  cuts word = Array.range (-2) (length word + 2) <#> \at -> take at word <> "|" <> drop at word <> "|" <> drop (at + 1) word <> "|" <> take (at - 1) word

oneLetterAway :: String -> Array String
oneLetterAway word = do
  position <- Array.range 0 (length word - 1)
  letter <- [ 'x', 'y', '\xE9' ]
  guard (charAt position word /= pure letter)
  pure (take position word <> singleton letter <> drop (position + 1) word)
