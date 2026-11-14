module Compat.Exotic.Nested where

import Prelude

import Data.Array as Array
import Effect (Effect)
import Effect.Console (log)

data Nested a = Flat a | Nest (Nested (Array a))

depth :: forall a. Nested a -> Int
depth (Flat _) = 0
depth (Nest inner) = 1 + depth inner

flatten :: forall a. Nested a -> Array a
flatten = go Array.singleton
  where
  go :: forall b. (b -> Array a) -> Nested b -> Array a
  go f (Flat b) = f b
  go f (Nest inner) = go (Array.concatMap f) inner

data Perfect a = Zero a | Succ (Perfect { left :: a, right :: a })

leaves :: forall a. Perfect a -> Int
leaves = go 1
  where
  go :: forall b. Int -> Perfect b -> Int
  go n (Zero _) = n
  go n (Succ inner) = go (n * 2) inner

mapPerfect :: forall a b. (a -> b) -> Perfect a -> Perfect b
mapPerfect f (Zero a) = Zero (f a)
mapPerfect f (Succ inner) = Succ (mapPerfect (\{ left, right } -> { left: f left, right: f right }) inner)

showPolymorphic :: forall a. Show a => Int -> a -> String
showPolymorphic 0 a = show a
showPolymorphic n a = showPolymorphic (n - 1) [ a ]

main :: Effect Unit
main = do
  let nested = Nest (Nest (Flat [ [ 1, 2 ], [ 3 ] ]))
  log (show (depth nested) <> " " <> show (flatten nested))
  log (show (leaves (Succ (Succ (Zero { left: { left: 1, right: 2 }, right: { left: 3, right: 4 } })))))
  log (show (leaves (mapPerfect show (Succ (Zero { left: 1, right: 2 })))))
  log (showPolymorphic 3 'x')
