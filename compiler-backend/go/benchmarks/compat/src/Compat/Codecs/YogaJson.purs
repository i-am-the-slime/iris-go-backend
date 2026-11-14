module Compat.Codecs.YogaJson where

import Prelude

import Data.Either (Either(..))
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
import Data.Show.Generic (genericShow)
import Data.Nullable (Nullable, toNullable)
import Effect (Effect)
import Effect.Console (log)
import Yoga.JSON (class ReadForeign, class WriteForeign, readJSON, writeJSON, readImpl, writeImpl)
import Yoga.JSON.Generics (genericReadForeignTaggedSum, genericWriteForeignTaggedSum, defaultOptions, genericReadForeignEnum, genericWriteForeignEnum)

data Status = Active | Suspended | Deleted

derive instance Generic Status _
instance Show Status where
  show = genericShow
instance ReadForeign Status where
  readImpl = genericReadForeignEnum { toConstructorName: identity }
instance WriteForeign Status where
  writeImpl = genericWriteForeignEnum { toConstructorName: identity }

data Message = Text { body :: String } | Ping

derive instance Generic Message _
instance Show Message where
  show = genericShow
instance ReadForeign Message where
  readImpl = genericReadForeignTaggedSum defaultOptions
instance WriteForeign Message where
  writeImpl = genericWriteForeignTaggedSum defaultOptions

type Account = { id :: Int, status :: Status, inbox :: Array Message, nickname :: Maybe String, legacy :: Nullable Int }

main :: Effect Unit
main = do
  let account = { id: 7, status: Suspended, inbox: [ Text { body: "hi" }, Ping ], nickname: Nothing, legacy: toNullable (Just 3) } :: Account
  let json = writeJSON account
  log json
  case readJSON json of
    Right (decoded :: Account) -> log (show decoded.status <> " " <> show decoded.inbox <> " " <> show decoded.nickname)
    Left errors -> log (show errors)
  log (show (readJSON """{"id":1,"status":"Gone","inbox":[],"legacy":null}""" :: Either _ Account) # const "rejected")
