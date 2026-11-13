module Main where

import Prelude


newtype Poly = Poly (forall a. a -> a)

use :: Poly -> Int
use (Poly f) = f 1 + (if f false then 0 else 2)

data Nested a = Flat a | Deep (Nested (Array a))

depth :: forall a. Nested a -> Int
depth = case _ of
  Flat _ -> 0
  Deep inner -> 1 + depth inner

main :: Array Int
main = [ use (Poly identity), depth (Deep (Deep (Flat [ [ 1 ] ]))) ]
