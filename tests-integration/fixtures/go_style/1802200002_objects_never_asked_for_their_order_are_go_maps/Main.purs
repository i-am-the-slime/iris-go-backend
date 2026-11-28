module Main where

import Prelude

import Control.Monad.ST as ST
import Data.Foldable (foldl)
import Data.Maybe (Maybe(..), maybe)
import Data.String as String
import Data.Tuple (Tuple)
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Effect.Console (log)
import Foreign.Object (Object)
import Foreign.Object as Object
import Foreign.Object.ST as STObject

words :: Array String
words = [ "pear", "fig", "pear", "kiwi", "fig", "pear", "10", "2" ]

counted :: Array String -> Object Int
counted = foldl (\counts word -> Object.alter (Just <<< maybe 1 (_ + 1)) word counts) Object.empty

describe :: Object Int -> String
describe counts = show (Object.lookup "pear" counts) <> " " <> show (Object.member "plum" counts) <> " " <> show (Object.size counts) <> " " <> show (Object.isEmpty counts)

lengths :: Unit -> Object Int
lengths _ = Object.fromFoldable (words <#> \word -> word /\ String.length word)

main :: Effect Unit
main = do
  log "-- lookups after inserts and deletes"
  log (describe (Object.delete "fig" (Object.insert "plum" 0 (counted words))))
  log (describe (Object.update (\count -> if count > 2 then Nothing else Just count) "pear" (counted words)))
  log "-- built from an array"
  let tallied = Object.fromFoldableWith (+) (words <#> \word -> word /\ 1)
  log (show (Object.lookup "pear" tallied) <> " " <> show (Object.lookup "fig" tallied) <> " " <> show (Object.size tallied))
  log "-- a thunk run twice builds two objects"
  let first = Object.insert "plum" 4 (lengths unit)
  let second = lengths unit
  log (show (Object.lookup "plum" first) <> " " <> show (Object.lookup "plum" second) <> " " <> show (Object.size second))
  log "-- filled in ST"
  let filled = Object.runST do
        object <- STObject.new
        ST.foreach words \word -> void (STObject.poke word (String.length word) object)
        _ <- STObject.delete "kiwi" object
        found <- STObject.peek "fig" object
        _ <- STObject.poke "fig" (maybe 0 (_ * 10) found) object
        pure object
  log (show (Object.lookup "kiwi" filled) <> " " <> show (Object.lookup "fig" filled) <> " " <> show (Object.size filled))
  log "-- read in the order of the keys"
  log (show (Object.toAscUnfoldable (counted words) :: Array (Tuple String Int)))
