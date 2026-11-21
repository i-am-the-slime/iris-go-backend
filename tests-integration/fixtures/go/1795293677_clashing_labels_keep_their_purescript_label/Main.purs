module Main where

import Prelude

import Data.Either (Either(..))
import Yoga.JSON (class ReadForeign, class WriteForeign, readJSON, writeJSON)

type Pair = { "A" :: Int, a :: Int }

type Triple = { "A" :: Int, a :: String, "A2" :: Number }

type Header = { "content-type" :: String, content_type :: String }

roundTrip :: forall record. ReadForeign record => WriteForeign record => Show record => record -> String
roundTrip record = case readJSON (writeJSON record) of
  Left _ -> "bad"
  Right (read :: record) -> show read

main :: Array String
main = do
  let pair = { "A": 1, a: 2 } :: Pair
  let triple = { "A": 3, a: "three", "A2": 3.5 } :: Triple
  let header = { "content-type": "text/plain", content_type: "underscore" } :: Header
  [ roundTrip pair
  , roundTrip triple
  , roundTrip header
  , show (pair { "A" = 10 })
  , show (triple { a = "updated", "A2" = 0.5 })
  , show (header { "content-type" = "application/json" })
  ]
