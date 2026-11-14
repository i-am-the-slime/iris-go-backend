module Repro.HigherKindedData where

import Prelude

import Data.Identity (Identity(..))
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Effect (Effect)
import Effect.Console (log)

type User f = { name :: f String, age :: f Int }

complete :: User Maybe -> Maybe (User Identity)
complete user = ado
  name <- user.name
  age <- user.age
  in { name: Identity name, age: Identity age }

main :: Effect Unit
main = log (show (map (\u -> unwrap u.name <> " " <> show (unwrap u.age)) (complete { name: Just "Ann", age: Just 30 })))
