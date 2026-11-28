module Main where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Console (log)

newtype Transform = Transform (forall b. Maybe (Array b -> Array b))

reversing :: Transform
reversing = Transform (Just Array.reverse)

applyTo :: Transform -> Array Int -> Array Int
applyTo (Transform transform) numbers = case transform of
  Just f -> f numbers
  Nothing -> numbers

applyToStrings :: Transform -> Array String -> Array String
applyToStrings (Transform transform) strings = case transform of
  Just f -> f strings
  Nothing -> strings

main :: Effect Unit
main = do
  log (show (applyTo reversing [ 1, 2, 3 ]))
  log (show (applyToStrings reversing [ "a", "b" ]))
