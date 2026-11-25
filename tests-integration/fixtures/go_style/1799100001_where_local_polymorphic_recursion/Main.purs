module Main where

import Prelude

import Effect (Effect)
import Effect.Console (log)

data Nested a = Flat a | Nest (Nested (Array a))

showTopLevel :: forall a. Show a => Nested a -> String
showTopLevel (Flat x) = show x
showTopLevel (Nest inner) = showTopLevel inner

showLocal :: forall a. Show a => Nested a -> String
showLocal = go
  where
  go :: forall b. Show b => Nested b -> String
  go (Flat x) = show x
  go (Nest inner) = "Nest " <> go inner

depth :: forall a. Show a => String -> Nested a -> String
depth label nested = go 0 nested
  where
  go :: forall b. Show b => Int -> Nested b -> String
  go levels (Flat x) = label <> show levels <> " " <> show x
  go levels (Nest inner) = go (levels + 1) inner

main :: Effect Unit
main = do
  log (showTopLevel (Nest (Nest (Flat [ [ 1, 2 ] ]))))
  log (showLocal (Nest (Nest (Flat [ [ 1, 2 ] ]))))
  log (showLocal (Flat "flat"))
  log (depth "levels: " (Nest (Nest (Nest (Flat [ [ [ true ] ] ])))))
