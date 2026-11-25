module Main where

import Prelude

data Nested a = Flat a | Nest (Nested (Array a))

showLocal :: forall a. Show a => Nested a -> String
showLocal = go
  where
  go :: forall b. Show b => Nested b -> String
  go (Flat value) = show value
  go (Nest inner) = "Nest " <> go inner

labelled :: forall a. Show a => String -> Nested a -> String
labelled label nested = go nested
  where
  go :: forall b. Show b => Nested b -> String
  go (Flat value) = label <> show value
  go (Nest inner) = go inner

main :: Array String
main =
  [ showLocal (Flat 1)
  , showLocal (Nest (Nest (Flat [ [ 1, 2 ], [ 3 ] ])))
  , labelled "nested: " (Nest (Flat [ true ]))
  ]
