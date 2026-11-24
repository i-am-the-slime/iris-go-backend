module T.Studio where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Console (log)
import Record.Studio (mapRecord, mapRecordKind, mapUniformRecord, recordKeys, sequenceRecord, shrink, (//))

type Settings = { width :: Int, height :: Int, depth :: Int }

main :: Effect Unit
main = do
  let settings = { width: 3, height: -4, depth: 5 } :: Settings
  log (show (mapRecord (_ * 2) settings))
  log (show (mapRecord (show :: Int -> String) settings))
  log (show (mapUniformRecord (\n -> n > 0) settings))
  log (show (sequenceRecord { a: Just 1, b: Just "x", c: Just [ 1.5 ] } :: Maybe _))
  log (show (sequenceRecord { a: Just 1, b: (Nothing :: Maybe String) } :: Maybe _))
  log (show (sequenceRecord { a: Right 1 :: Either String Int, b: Left "bad" :: Either String Int, c: Left "worse" :: Either String Boolean } :: Either String _))
  log (show (sequenceRecord { xs: [ 1, 2 ], ys: [ "a", "b" ] } :: Array _))
  log (show (mapRecordKind (Array.head) { a: [ 1, 2 ], b: [ "z" ], c: ([] :: Array Boolean) }))
  log (show (recordKeys settings) <> show (recordKeys {}) <> show (recordKeys { z: 1, a: 2, "M": 3 }))
  log (show (shrink { a: 1, b: "two", c: 3.0 } :: { a :: Int, c :: Number }))
  log (show ({ a: 1, b: 2 } // { b: "override", c: true }))
