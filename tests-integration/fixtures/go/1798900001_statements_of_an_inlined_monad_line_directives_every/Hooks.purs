module Hooks where

import Prelude

import Effect (Effect)
import Effect.Ref as Ref

newtype Hooks a = Hooks (Int -> Effect a)

instance Functor Hooks where
  map f (Hooks run) = Hooks \key -> map f (run key)

instance Apply Hooks where
  apply = ap

instance Applicative Hooks where
  pure a = Hooks \_ -> pure a

instance Bind Hooks where
  bind (Hooks run) f = Hooks \key -> run key >>= f >>> runHooks key

instance Monad Hooks

runHooks :: forall a. Int -> Hooks a -> Effect a
runHooks key (Hooks run) = run key

useState :: forall a. a -> Hooks (Ref.Ref a)
useState initial = Hooks \_ -> Ref.new initial

useKey :: Int -> Effect Unit -> Hooks Unit
useKey wanted action = Hooks \key -> when (key == wanted) action

component :: Int -> (Unit -> Hooks Unit) -> Effect Unit
component key body = runHooks key (body unit)
