module Main where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Effect (Effect)

data Outcome failure success = Failed failure | Succeeded success

describe :: forall failure success. Show failure => Show success => Outcome failure success -> String
describe = case _ of
  Failed failure -> "failed with " <> show failure
  Succeeded success -> "succeeded with " <> show success

describeAll :: forall failure success. Show failure => Show success => Array (Outcome failure success) -> String
describeAll outcomes = describeFrom 0 ""
  where
  describeFrom index text = case Array.index outcomes index of
    Nothing -> text
    Just outcome -> describeFrom (index + 1) (text <> describe outcome <> "; ")

countAll :: forall a. Array a -> Int
countAll values = countFrom 0
  where
  countFrom index = case Array.index values index of
    Nothing -> index
    Just _ -> countFrom (index + 1)

main :: Effect (Array String)
main = pure
  [ describeAll [ Failed "timeout", Succeeded 3 ]
  , describeAll [ Succeeded true, Failed "refused" ]
  , describeAll [ Failed 404, Succeeded false ]
  , show (countAll [ 1.5, 2.5 ])
  ]
