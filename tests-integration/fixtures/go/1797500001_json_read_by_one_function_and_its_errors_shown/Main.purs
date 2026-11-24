module Main where

import Prelude

import Data.Either (Either(..))
import Yoga.JSON (readJSON)

type Todo = { title :: String, done :: Boolean, tags :: Array String }

describe :: String -> String
describe text = case readJSON text of
  Left errors -> "bad: " <> show errors
  Right (todo :: Todo) -> todo.title

describeAgain :: String -> String
describeAgain text = case readJSON text of
  Left errors -> "bad again: " <> show errors
  Right (todo :: Todo) -> show todo.done

main :: Array String
main =
  [ describe """{ "title": "write docs", "done": false, "tags": ["iris"] }"""
  , describe """{ "title": 1, "done": "no", "tags": ["iris", 2] }"""
  , describeAgain """{ "done": true }"""
  ]
