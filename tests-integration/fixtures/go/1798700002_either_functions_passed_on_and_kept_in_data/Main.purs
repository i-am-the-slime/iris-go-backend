module Main where

import Prelude

import Control.Monad.Error.Class (throwError, try)
import Control.Monad.Except (ExceptT(..), runExceptT)
import Data.Array as Array
import Data.Either (Either(..), either)
import Data.Foldable (foldM)
import Effect (Effect)
import Effect.Class (liftEffect)
import Effect.Console (log)
import Effect.Exception (throw)
import Effect.Ref as Ref

type Step = Int -> ExceptT String Effect Int

halve :: Step
halve n
  | n `mod` 2 == 0 = pure (n / 2)
  | otherwise = throwError ("odd " <> show n)

addOne :: Step
addOne n = pure (n + 1)

twice :: Step -> Int -> ExceptT String Effect Int
twice step n = do
  once <- step n
  step once

retrying :: Int -> Step -> Int -> ExceptT String Effect Int
retrying attempts step n = do
  result <- liftEffect (runExceptT (step n))
  case result of
    Right value -> pure value
    Left problem
      | attempts <= 1 -> throwError problem
      | otherwise -> retrying (attempts - 1) step (n + 1)

pipeline :: Array Step
pipeline = [ addOne, halve, twice addOne ]

runAll :: Int -> ExceptT String Effect Int
runAll start = foldM (\value step -> step value) start pipeline

fromEffect :: Effect Int -> ExceptT String Effect Int
fromEffect action = ExceptT (either (const (Left "thrown")) Right <$> try action)

main :: Effect Unit
main = do
  counter <- Ref.new 0
  let
    counted :: Step
    counted n = do
      liftEffect (Ref.modify_ (_ + 1) counter)
      halve n
  a <- runExceptT (twice halve 8)
  log (show a)
  b <- runExceptT (twice halve 6)
  log (show b)
  c <- runExceptT (twice (\n -> if n > 100 then throwError "big" else pure (n * 10)) 7)
  log (show c)
  d <- runExceptT (retrying 3 counted 5)
  log (show d)
  e <- runExceptT (retrying 2 counted 1)
  log (show e)
  calls <- Ref.read counter
  log (show calls)
  f <- runExceptT (runAll 3)
  log (show f)
  g <- runExceptT (runAll 4)
  log (show g)
  h <- runExceptT (fromEffect (throw "no"))
  log (show h)
  i <- runExceptT (fromEffect (pure 5) >>= halve)
  log (show i)
  log (show (Array.length pipeline))
