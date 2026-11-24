module Repro.R06 where

import Prelude

import Effect (Effect)
import Effect.Console (log)

newtype Task a = Task (Effect a)

runTask :: forall a. Task a -> Effect a
runTask (Task effect) = effect

instance Functor Task where
  map f (Task effect) = Task (map f effect)

instance Apply Task where
  apply = ap

instance Applicative Task where
  pure = Task <<< pure

instance Bind Task where
  bind (Task effect) next = Task (map next effect >>= runTask)

instance Monad Task

main :: Effect Unit
main = do
  sum <- runTask ((+) <$> pure 1 <*> pure 2)
  log (show sum)
