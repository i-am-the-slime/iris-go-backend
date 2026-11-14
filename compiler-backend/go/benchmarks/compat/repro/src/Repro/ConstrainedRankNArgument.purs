module Repro.ConstrainedRankNArgument where

import Prelude

import Effect (Effect)
import Effect.Console (log)

type Lens s a = forall f. Functor f => (a -> f a) -> s -> f s

newtype Id a = Id a

instance Functor Id where
  map f (Id a) = Id (f a)

first :: forall a b. Lens { first :: a, second :: b } a
first f record = map (\a -> record { first = a }) (f record.first)

set :: forall s a. Lens s a -> a -> s -> s
set lens a s = case lens (\_ -> Id a) s of
  Id result -> result

main :: Effect Unit
main = do
  log (show (set first 99 { first: 1, second: "s" }))
  log (show (set first "x" { first: "y", second: 2 }))
