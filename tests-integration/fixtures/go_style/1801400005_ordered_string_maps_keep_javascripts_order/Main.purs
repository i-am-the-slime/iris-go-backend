module Fun.OrderedStrings where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.String.CodeUnits as CodeUnits
import Data.Tuple.Nested (type (/\), (/\))
import Effect (Effect)
import Effect.Console (log)

main :: Effect Unit
main = do
  log "-- words with astral, private-use and lone-surrogate letters, taken least first"
  log (show (leastFirst letters))
  log "-- greatest first, after the plain words were in the map alone for a while"
  log (show (greatestFirst (plain <> letters <> plain)))
  log "-- the words next to each probe, the probes holding the letters the map does not"
  log (show (nextTo (Array.drop 3 letters) (letters <> [ "\x1F601", "\xE001", "\xFFFF\xFFFF", "\xD7FF" ])))
  log "-- the entries in order once the least two are gone"
  log (show (Map.toUnfoldable (withoutLeastTwo (letters <> plain)) :: Array (String /\ Int)))

letters :: Array String
letters = [ "b", "\x1F600", "a", "\xE000", "\xF8FF", "\xFFFF", "\x10FFFF", "ab", "", "a\x1F600", "a\xE000", "\xD800", "\xDC00", "\xDBFF\xDFFF", "\x1F600" <> "a", "\xE000a", "z", "\x7F", "\x80", "\x7FF", "\x800", "\xD7FF" ]

plain :: Array String
plain = [ "kiwi", "apple", "fig", "banana", "cherry", "date", "elder", "grape" ]

leastFirst :: Array String -> Array String
leastFirst words = go [] (foldl (\map word -> Map.insert word (CodeUnits.length word) map) Map.empty words)
  where
  go taken map = case Map.findMin map of
    Nothing -> taken
    Just { key } -> go (Array.snoc taken key) (Map.delete key map)

greatestFirst :: Array String -> Array String
greatestFirst words = go [] (foldl (\map word -> Map.insert word unit map) Map.empty words)
  where
  go taken map = case Map.findMax map of
    Nothing -> taken
    Just { key } -> go (Array.snoc taken key) (Map.delete key map)

nextTo :: Array String -> Array String -> Array String
nextTo words probes = (foldl step { shown: [], map: Map.empty } probes).shown
  where
  step { shown, map } probe = do
    let grown = foldl (\m word -> Map.insert word unit m) map words
    let found = [ _.key <$> Map.lookupLT probe grown, _.key <$> Map.lookupLE probe grown, _.key <$> Map.lookupGE probe grown, _.key <$> Map.lookupGT probe grown ]
    { shown: Array.snoc shown (show found), map: Map.delete probe grown }

withoutLeastTwo :: Array String -> Map String Int
withoutLeastTwo words = drop (drop (foldl (\map word -> Map.insert word (CodeUnits.length word) map) Map.empty words))
  where
  drop map = case Map.findMin map of
    Just { key } -> Map.delete key map
    Nothing -> map
