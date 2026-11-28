module Main where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Console (log)

type Transform = forall b. Maybe (Array b -> Array b)

type Settings = { transform :: Transform, label :: String }

untouched :: Settings
untouched = { transform: Nothing, label: "untouched" }

withTransform :: Transform -> Settings -> Settings
withTransform t settings = settings { transform = t }

applyTo :: Settings -> Array Int -> Array Int
applyTo settings numbers = case settings.transform of
  Just transform -> transform numbers
  Nothing -> numbers

main :: Effect Unit
main = do
  let reversing = withTransform (Just Array.reverse) untouched
  log (show (applyTo reversing [ 1, 2, 3 ]))
