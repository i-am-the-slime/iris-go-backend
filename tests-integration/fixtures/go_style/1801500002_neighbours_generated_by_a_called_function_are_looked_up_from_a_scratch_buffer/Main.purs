module Fun.Candidates where

import Prelude

import Control.Alternative (guard)
import Data.Array as Array
import Data.Char (fromCharCode)
import Data.Set (Set)
import Data.Set as Set
import Data.String.CodeUnits (charAt, drop, length, singleton, take)
import Effect (Effect)
import Effect.Console (log)

main :: Effect Unit
main = do
  log "-- the steps of a ladder climbed a level at a time, halves of a surrogate pair joining"
  log (show (ladderLength "x\xD83Da" "b\xD83D\xDE00" [ "x\xD83D\xDE00", "a\xD83D\xDE00", "ab\xDE00", "b\xD83D\xDE00", "bb\xDE00" ]))
  log (show (ladderLength "xa\xDE00" "bb\xDE00" [ "x\xD83D\xDE00", "a\xD83D\xDE00", "ab\xDE00", "b\xD83D\xDE00", "bb\xDE00" ]))
  log (show (ladderLength "aaaa" "bbbb" [ "abaa", "abba", "bbba", "bbbb" ]))
  log (show (ladderLength "aaaa" "bbbb" [ "abaa", "bbbb" ]))
  log "-- the words one letter away from a word that are not in a dictionary"
  log (show (unknownNeighbours "ab" [ "bb", "aa", "a\xD83D" ]))
  log "-- the guard keeps a value it hands on"
  log (show ([ "ab", "", "abcd" ] >>= \word -> if length word > 1 then [ word <> "!" ] else []))

ladderLength :: String -> String -> Array String -> Int
ladderLength begin end words = climb 1 [ begin ] (Set.delete begin (Set.fromFoldable words))
  where
  climb :: Int -> Array String -> Set String -> Int
  climb steps level unvisited
    | Array.null level = 0
    | Array.elem end level = steps
    | otherwise = do
        let reached = Set.fromFoldable (Array.filter (_ `Set.member` unvisited) (level >>= oneLetterAway))
        climb (steps + 1) (Set.toUnfoldable reached) (unvisited `Set.difference` reached)

oneLetterAway :: String -> Array String
oneLetterAway word = do
  position <- Array.range 0 (length word - 1)
  letter <- alphabet
  guard (charAt position word /= pure letter)
  pure (take position word <> singleton letter <> drop (position + 1) word)

unknownNeighbours :: String -> Array String -> Array String
unknownNeighbours word known = do
  let dictionary = Set.fromFoldable known
  position <- Array.range 0 (length word - 1)
  letter <- alphabet
  let candidate = take position word <> singleton letter <> drop (position + 1) word
  guard (candidate /= word && not (Set.member candidate dictionary))
  pure candidate

alphabet :: Array Char
alphabet = [ 'a', 'b' ] <> Array.mapMaybe fromCharCode [ 0xD83D, 0xDE00 ]
