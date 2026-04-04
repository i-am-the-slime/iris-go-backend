module Main where

import Prelude

import Effect (Effect)
import Effect.Console (log)

main :: Effect Unit
main = do
  log "Hello, PureScript!"
  log "This is a test project for purescript-analyzer"

greet :: String -> String
greet name = "Hello, " <> name <> "!"

add :: Int -> Int -> Int
add x y = x + y