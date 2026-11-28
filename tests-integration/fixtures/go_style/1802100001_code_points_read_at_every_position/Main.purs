module Main where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.String as String
import Data.String.CodePoints (CodePoint, codePointFromChar)
import Data.String.CodeUnits as CodeUnits
import Effect (Effect)
import Effect.Console (log)

main :: Effect Unit
main = do
  log "-- every position from before the start to past the end"
  each texts \text -> log (show (pointsAround text))
  log "-- the first code point, read at a position that is not a literal"
  each texts \text -> log (show (pointAt (CodeUnits.length text - CodeUnits.length text) text))
  log "-- positions that hold an a"
  each texts \text -> log (show (positionsOfA text))
  where
  each :: forall a. Array a -> (a -> Effect Unit) -> Effect Unit
  each values act = void (Array.foldM (\_ value -> act value) unit values)
  texts = [ "", "a", "\xD83D", "\xDE00", "a\xD83D", "\xD83D-b", "\x1F600", "x\x1F600y", "\xE9t\xE9 a", "ab\xDE00\xD83D", "\xD83D\xD83D\xDE00" ]

pointsAround :: String -> Array (Maybe CodePoint)
pointsAround text = Array.range (-2) (String.length text + 1) <#> \position -> String.codePointAt position text

pointAt :: Int -> String -> Maybe CodePoint
pointAt position text = String.codePointAt position text

positionsOfA :: String -> Array Int
positionsOfA text = Array.filter isA (Array.range (-1) (String.length text))
  where
  isA position = String.codePointAt position text == Just (codePointFromChar 'a')
