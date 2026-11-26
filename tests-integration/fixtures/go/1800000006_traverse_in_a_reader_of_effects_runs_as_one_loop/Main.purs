module Main where

import Prelude

import Data.Array as Array
import Data.Either (Either(..), either)
import Data.Traversable (traverse)
import Effect (Effect)
import Effect.Ref as Ref
import Journal (log)

newtype Fallible a = Fallible (Unit -> Effect (Either String a))

run :: forall a. Fallible a -> Effect (Either String a)
run (Fallible action) = action unit

instance Functor Fallible where
  map f (Fallible action) = Fallible \context -> map (map f) (action context)

instance Apply Fallible where
  apply = ap

instance Applicative Fallible where
  pure value = Fallible \_ -> pure (Right value)

instance Bind Fallible where
  bind (Fallible action) next = Fallible \context -> do
    result <- action context
    case result of
      Left problem -> pure (Left problem)
      Right value -> run (next value)

instance Monad Fallible

lift :: forall a. Effect a -> Fallible a
lift action = Fallible \_ -> Right <$> action

failWith :: forall a. String -> Fallible a
failWith problem = Fallible \_ -> pure (Left problem)

main :: Effect Unit
main = do
  doubled <- run (traverse (\number -> pure (number * 2)) (Array.range 1 5))
  log (shown doubled)
  seen <- Ref.new 0
  counted <- run (traverse (counting seen) (Array.range 1 5))
  log (shown counted)
  stopped <- run (traverse (counting seen >=> failingAt 3) (Array.range 1 5))
  log (shown stopped)
  Ref.read seen >>= show >>> log
  where
  counting seen number = lift (Ref.modify_ (_ + 1) seen) $> number * 10
  failingAt limit number
    | number >= limit * 10 = failWith ("stopped at " <> show number)
    | otherwise = pure number
  shown = either ("failed: " <> _) show
