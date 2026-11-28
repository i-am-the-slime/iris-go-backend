module Fun.OrderedStringRuns where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.String.CodeUnits as CodeUnits
import Data.Tuple.Nested (type (/\))
import Effect (Effect)
import Effect.Console (log)

main :: Effect Unit
main = do
  log "-- words ascending by their code units, astral after private-use, with the least taken now and then"
  log (show (Map.toUnfoldable (queued ascending) :: Array (String /\ Int)))
  log "-- the words next to probes between them, astral, private-use and lone surrogates among them"
  log (show (probes <#> \probe -> nextTo probe (queued ascending)))
  log "-- the same words with a new one below the greatest, and with a held one changed"
  log (show (Map.toUnfoldable (Map.insert "\xD7FF\xD7FF" 0 (queued ascending)) :: Array (String /\ Int)))
  log (show (Map.toUnfoldable (Map.insert "\x1F600" 0 (queued ascending)) :: Array (String /\ Int)))
  log "-- words ascending by their bytes but not their code units"
  log (show (Map.toUnfoldable (queued byBytes) :: Array (String /\ Int)))

-- | Twenty words in the order of their UTF-16 code units, where U+E000 and up come after the
-- | astral characters' surrogates.
ascending :: Array String
ascending = [ "", "a", "a\x1F600", "a\xE000", "a\xFFFF", "b", "z", "\x7F", "\x80", "\x7FF", "\x800", "\xD7FF", "\xD800", "\x10000", "\x1F600", "\x1F600" <> "a", "\xDBFF\xDFFF", "\xDC00", "\xE000", "\xE000" <> "a", "\xF8FF", "\xFFFF", "\xFFFF\x1F600" ]

-- | Words in the order of their UTF-8 bytes, which puts the astral ones last.
byBytes :: Array String
byBytes = [ "a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o", "p", "\xE000", "\xFFFF", "\x10000", "\x1F600", "\x10FFFF" ]

queued :: Array String -> Map String Int
queued words = foldl step Map.empty (Array.mapWithIndex (\at word -> { at, word }) words)
  where
  step map { at, word } = do
    let grown = Map.insert word (CodeUnits.length word) map
    case Map.findMin grown of
      Just { key } | at `mod` 6 == 5 -> Map.delete key grown
      _ -> grown

probes :: Array String
probes = [ "", "0", "a\x1F601", "a\xE001", "aa", "\xD7FF\xD7FF", "\xD800", "\xD800\xDC00", "\xDBFF", "\xDBFF\xDFFF", "\xDBFF\xE000", "\xDFFF", "\xE000", "\xEFFF", "\xFFFE", "\xFFFF", "\xFFFF\xFFFF" ]

nextTo :: String -> Map String Int -> String
nextTo probe map = show (_.key <$> Map.lookupLT probe map) <> show (_.key <$> Map.lookupLE probe map) <> show (_.key <$> Map.lookupGE probe map) <> show (_.key <$> Map.lookupGT probe map)
