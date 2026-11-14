module Compat.Codecs.CodecArgonaut where

import Prelude

import Data.Argonaut.Core (stringify)
import Data.Argonaut.Parser (jsonParser)
import Data.Codec.Argonaut (JsonCodec, printJsonDecodeError)
import Data.Codec.Argonaut as CA
import Data.Codec.Argonaut.Common as CAC
import Data.Codec.Argonaut.Record as CAR
import Data.Codec.Argonaut.Sum as CAS
import Data.Codec.Argonaut.Variant as CAV
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Variant (Variant, inj)
import Data.Profunctor (dimap)
import Effect (Effect)
import Effect.Console (log)
import Type.Proxy (Proxy(..))

type Book = { title :: String, pages :: Int, tags :: Array String, sequel :: Maybe String, rating :: Number }

book :: JsonCodec Book
book = CA.object "Book" $ CAR.record
  { title: CA.string
  , pages: CA.int
  , tags: CA.array CA.string
  , sequel: CAC.maybe CA.string
  , rating: CA.number
  }

data Colour = Red | Green | Blue

colour :: JsonCodec Colour
colour = CAS.enumSum print parse
  where
  print = case _ of
    Red -> "red"
    Green -> "green"
    Blue -> "blue"
  parse = case _ of
    "red" -> Just Red
    "green" -> Just Green
    "blue" -> Just Blue
    _ -> Nothing

type Shape = Variant (circle :: Number, rectangle :: { width :: Number, height :: Number })

shape :: JsonCodec Shape
shape = CAV.variantMatch
  { circle: Right CA.number
  , rectangle: Right (CAR.object "Rectangle" { width: CA.number, height: CA.number })
  }

main :: Effect Unit
main = do
  let original = { title: "Dune", pages: 412, tags: [ "sf", "classic" ], sequel: Just "Dune Messiah", rating: 4.5 }
  let encoded = CA.encode book original
  log (stringify encoded)
  log (show (map _.title (CA.decode book encoded)))
  case jsonParser """{"title":"X","pages":"many","tags":[],"sequel":null,"rating":1}""" of
    Left error -> log error
    Right json -> log (either' (CA.decode book json))
  log (stringify (CA.encode (CA.array colour) [ Red, Blue ]))
  log (stringify (CA.encode shape (inj (Proxy @"circle") 1.5)))
  log (stringify (CA.encode shape (inj (Proxy @"rectangle") { width: 2.0, height: 3.0 })))
  log (stringify (CA.encode (CAC.either CA.int CA.string) (Left 3)))
  log (stringify (CA.encode (dimap show (const 0) CA.string) 99))
  where
  either' = case _ of
    Left error -> "error: " <> printJsonDecodeError error
    Right value -> "decoded " <> value.title
