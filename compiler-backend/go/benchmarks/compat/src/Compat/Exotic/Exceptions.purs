module Compat.Exotic.Exceptions where

import Prelude

import Data.Either (Either(..))
import Effect (Effect)
import Effect.Console (log)
import Effect.Exception (catchException, error, message, throw, throwException, try)
import Effect.Ref as Ref
import Data.Traversable as Data.Traversable

risky :: Int -> Effect Int
risky n
  | n > 2 = throw ("too big: " <> show n)
  | otherwise = pure (n * 10)

main :: Effect Unit
main = do
  results <- traverse' (\n -> try (risky n)) [ 1, 2, 3 ]
  log (show (map (case _ of
    Left e -> "error " <> message e
    Right v -> show v) results))
  recovered <- catchException (\e -> pure ("caught " <> message e)) (throwException (error "direct") *> pure "unreached")
  log recovered
  ref <- Ref.new 0
  _ <- try do
    Ref.modify_ (_ + 1) ref
    _ <- throw "midway"
    Ref.modify_ (_ + 100) ref
  seen <- Ref.read ref
  log (show seen)
  nested <- try (catchException (\_ -> throw "rethrown") (throw "inner"))
  log (case nested of
    Left e -> message e
    Right (_ :: Unit) -> "no")
  where
  traverse' f xs = Data.Traversable.traverse f xs
