module Main where

import Prelude

type Lens s a = forall f. Functor f => (a -> f a) -> s -> f s

newtype Identity a = Identity a

instance Functor Identity where
  map f (Identity a) = Identity (f a)

newtype Const r a = Const r

instance Functor (Const r) where
  map _ (Const r) = Const r

first :: forall a b. Lens { first :: a, second :: b } a
first f record = map (\a -> record { first = a }) (f record.first)

set :: forall s a. Lens s a -> a -> s -> s
set lens a s = case lens (\_ -> Identity a) s of
  Identity result -> result

view :: forall s a. Lens s a -> s -> a
view lens s = case lens Const s of
  Const a -> a

main :: Array Int
main =
  [ (set first 99 { first: 1, second: "s" }).first
  , view first { first: 7, second: true }
  , view first (set first 3 { first: 0, second: unit })
  ]
