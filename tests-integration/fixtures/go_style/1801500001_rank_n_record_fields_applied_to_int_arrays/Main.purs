module Main where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Console (log)

type Transform = forall b. Maybe (Array b -> Array b)

type Settings = { transform :: Transform, label :: String }

reversing :: Settings
reversing = { transform: Just Array.reverse, label: "reversed" }

untouched :: Settings
untouched = { transform: Nothing, label: "untouched" }

applyTo :: Settings -> Array Int -> Array Int
applyTo settings numbers = case settings.transform of
  Just transform -> transform numbers
  Nothing -> numbers

main :: Effect Unit
main = do
  log (reversing.label <> " " <> show (applyTo reversing [ 1, 2, 3 ]))
  log (untouched.label <> " " <> show (applyTo untouched [ 1, 2, 3 ]))
  case reversing.transform of
    Just transform -> log (show (transform [ "a", "b" ]))
    Nothing -> pure unit
