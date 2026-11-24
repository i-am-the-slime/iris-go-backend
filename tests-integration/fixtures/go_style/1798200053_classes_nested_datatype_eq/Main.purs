module T.NestEq where

import Prelude

import Effect (Effect)
import Effect.Console (log)

data Nested a = Flat a | Nest (Nested (Array a))
derive instance Eq a => Eq (Nested a)

main :: Effect Unit
main = log (show (Nest (Flat [ 1 ]) == Nest (Flat [ 1 ])))
