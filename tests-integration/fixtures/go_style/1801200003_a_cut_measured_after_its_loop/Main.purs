module Main where

import Prelude

import Data.Maybe (Maybe(..))
import Data.String as String
import Data.String.CodeUnits (drop, indexOf', take)
import Data.String.Pattern (Pattern(..))
import Effect (Effect)
import Effect.Console (log)

main :: Effect Unit
main = do
  log "-- the column after the last line break, measured once the loop is done"
  log (show (texts <#> columnAfter))
  log (show (texts <#> headAfter))
  where
  texts = [ [ "one", "two", "three" ], [ "no breaks" ], [ "caf\xE9", "\x1F600!" ], [] ] <#> String.joinWith "\n"

columnAfter :: String -> Int
columnAfter text = go 0 0
  where
  go lines at = case indexOf' (Pattern "\n") at text of
    Just found -> go (lines + 1) (found + 1)
    Nothing
      | lines == 0 -> String.length text
      | otherwise -> String.length (drop at text) + lines

headAfter :: String -> String
headAfter text = go 0
  where
  go at = case indexOf' (Pattern "\n") at text of
    Just found -> go (found + 1)
    Nothing -> take (at + 2) text <> "|" <> show (String.length (take at text))
