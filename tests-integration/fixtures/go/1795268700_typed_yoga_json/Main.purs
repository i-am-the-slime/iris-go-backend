module Main where

import Prelude

import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Nullable (Nullable)
import Foreign.Object (Object)
import Yoga.JSON (readJSON, writeJSON)

type Item = { id :: Int, name :: String, note :: Maybe String, label :: Nullable Number, tags :: Array (Maybe Boolean), extra :: Object Int }

readItems :: String -> Either String (Array Item)
readItems text = case readJSON text of
  Left _ -> Left "rejected"
  Right items -> Right items

writeItems :: Array Item -> String
writeItems = writeJSON

main :: Array String
main = case readItems """[{"id":1,"name":"a","label":null,"tags":[true,null],"extra":{}}]""" of
  Left message -> [ message ]
  Right items -> [ writeItems items ]
