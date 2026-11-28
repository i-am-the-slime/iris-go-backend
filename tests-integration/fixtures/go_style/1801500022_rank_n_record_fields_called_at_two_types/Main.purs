module Main where

import Prelude

import Data.Array as Array
import Effect (Effect)
import Effect.Console (log)

type Settings = { transform :: forall b. Array b -> Array b, label :: String }

reversing :: Settings
reversing = { transform: Array.reverse, label: "reversed" }

main :: Effect Unit
main = do
  log (reversing.label <> " " <> show (reversing.transform [ 1, 2, 3 ]))
  log (show (reversing.transform [ "a", "b" ]))
