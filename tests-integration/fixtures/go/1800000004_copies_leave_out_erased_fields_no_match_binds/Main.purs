module Main where

import Prelude

import Effect (Effect)
import Journal (log)

data Nested a = Flat | Deep a (Nested (Array a))

depth :: forall a. Nested a -> Int
depth = case _ of
  Flat -> 0
  Deep _ rest -> 1 + depth rest

total :: forall a. Nested a -> Int
total = case _ of
  Flat -> 0
  Deep _ Flat -> 1
  Deep _ rest -> 2 + total rest

main :: Effect Unit
main = do
  log (show (depth (Deep 1 (Deep [ 2, 3 ] Flat))))
  log (show (total (Deep 1 (Deep [ 2, 3 ] (Deep [ [ 4 ] ] Flat)))))
