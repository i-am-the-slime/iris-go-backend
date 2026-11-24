module Main where

import Prelude

import Box (newBox, readBox)
import Effect (Effect)
import Effect.Console (log)

main :: Effect Unit
main = do
  let model = readBox (newBox { count: 1, name: "first", size: { width: 80, height: 24 } })
  log (model.name <> " " <> show model.count <> " " <> show model.size.width)
