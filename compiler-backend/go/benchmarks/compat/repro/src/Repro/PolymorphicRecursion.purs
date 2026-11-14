module Repro.PolymorphicRecursion where

import Prelude

import Effect (Effect)
import Effect.Console (log)

nest :: forall a. Show a => Int -> a -> String
nest 0 a = show a
nest n a = nest (n - 1) [ a ]

main :: Effect Unit
main = log (nest 3 'x')
