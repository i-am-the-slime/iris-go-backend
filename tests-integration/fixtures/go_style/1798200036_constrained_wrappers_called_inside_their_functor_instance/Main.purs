module Repro.R07 where

-- Generalisation of the known `<#>` bug: ANY constrained wrapper (here a user-defined `mapOver`)
-- called from main at Rose AND inside Functor Rose at Array (Rose) is rejected as polymorphic recursion.
import Prelude

import Effect (Effect)
import Effect.Console (log)

data Rose a = Rose a (Array (Rose a))

mapOver :: forall f a b. Functor f => f a -> (a -> b) -> f b
mapOver container f = map f container

instance Functor Rose where
  map f (Rose a kids) = Rose (f a) (mapOver kids (map f))

size :: forall a. Rose a -> Int
size (Rose _ kids) = 1 + sumSizes kids
  where
  sumSizes = case _ of
    [] -> 0
    _ -> 1

main :: Effect Unit
main = mapOver (Rose 1 [ Rose 2 [] ]) (_ + 1) # size # show # log
