module Compat.Codecs.ArgonautCodecs where

import Prelude

import Data.Argonaut.Core (stringify)
import Data.Argonaut.Decode (class DecodeJson, decodeJson, printJsonDecodeError, parseJson)
import Data.Argonaut.Encode (class EncodeJson, encodeJson)
import Data.Argonaut.Decode.Generic (genericDecodeJson)
import Data.Argonaut.Encode.Generic (genericEncodeJson)
import Data.Either (Either(..))
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
import Data.Show.Generic (genericShow)
import Data.Tuple.Nested (type (/\), (/\))
import Effect (Effect)
import Effect.Console (log)

data Event
  = Login { user :: String, at :: Int }
  | Logout String
  | Heartbeat

derive instance Generic Event _
instance Show Event where
  show = genericShow
instance EncodeJson Event where
  encodeJson = genericEncodeJson
instance DecodeJson Event where
  decodeJson = genericDecodeJson

main :: Effect Unit
main = do
  let record = { name: "widget", sizes: [ 1, 2, 3 ], meta: { active: true, score: Just 0.25 }, pair: "k" /\ 7 }
  let json = encodeJson record
  log (stringify json)
  log (show (decodeJson json :: Either _ { name :: String, sizes :: Array Int, meta :: { active :: Boolean, score :: Maybe Number }, pair :: String /\ Int }))
  log (stringify (encodeJson [ Login { user: "ann", at: 3 }, Logout "bob", Heartbeat ]))
  log (show (decodeJson (encodeJson [ Logout "x", Heartbeat ]) :: Either _ (Array Event)))
  case parseJson """{"name": 3}""" of
    Left error -> log (printJsonDecodeError error)
    Right parsed -> log (either' (decodeJson parsed :: Either _ { name :: String }))
  where
  either' = case _ of
    Left error -> printJsonDecodeError error
    Right value -> value.name
