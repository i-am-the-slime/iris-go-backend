module Main where

import Prelude

import Data.Foldable (foldl)
import Data.FoldableWithIndex (foldlWithIndex)
import Data.Maybe (Maybe(..), maybe)
import Data.Tuple (Tuple)
import Effect (Effect)
import Effect.Console (log)
import Foreign.Object (Object)
import Foreign.Object as Object

words :: Array String
words = [ "pear", "fig", "2", "pear", "kiwi", "10", "fig" ]

counted :: Array String -> Object Int
counted = foldl (\counts word -> Object.alter (Just <<< maybe 1 (_ + 1)) word counts) Object.empty

inserted :: Array String -> Object Int
inserted = foldl (\table word -> Object.insert word 0 table) Object.empty

main :: Effect Unit
main = do
  log "-- the keys of an object that went through inserts, array indices first"
  log (show (Object.keys (Object.delete "fig" (Object.insert "apple" 1 (inserted words)))))
  log (show (Object.values (Object.insert "fig" 9 (counted words))))
  log "-- shown"
  log (show (counted words))
  log "-- folded in order"
  log (foldlWithIndex (\key text count -> text <> key <> "=" <> show count <> ";") "" (counted words))
  log "-- one function, read in order by one caller and looked up by another"
  log (show (Object.lookup "pear" (counted words)) <> " " <> show (Object.toUnfoldable (counted words) :: Array (Tuple String Int)))
