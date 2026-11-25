module Main where

import Prelude

import Effect (Effect)
import Journal (log)

type Continuation f a = forall r. (a -> f r) -> f r

newtype Resource a = Resource (Continuation Effect a)

with :: forall a r. Resource a -> (a -> Effect r) -> Effect r
with = case _ of
  Resource continue -> continue

acquired :: Resource Int
acquired = Resource \use -> do
  log "acquire"
  result <- use 41
  log "release"
  pure result

main :: Effect Unit
main = do
  n <- with acquired \x -> pure (x + 1)
  log (show n)
  with acquired \x -> log (show x)
