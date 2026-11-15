module Main where

import Prelude

data Nested a = Flat a | Nest (Nested (Array a))

showNested :: forall a. Show a => Nested a -> String
showNested (Flat value) = show value
showNested (Nest inner) = "Nest " <> showNested inner

main :: Array String
main = [ showNested (Flat 1), showNested (Nest (Nest (Flat [ [ 1, 2 ], [ 3 ] ]))) ]
