module Main where

import Prelude

import Control.Monad.Error.Class (throwError)
import Control.Monad.Except (ExceptT, runExceptT)
import Data.Either (Either(..))
import Effect (Effect)
import Effect.Class (liftEffect)
import Journal (log)

classify :: Int -> ExceptT String Effect (Either Int Int)
classify n
  | n < 0 = throwError ("negative " <> show n)
  | n > 100 = classify (n - 100)
  | n `mod` 2 == 0 = pure (Left (n / 2))
  | otherwise = pure (Right (n * 3 + 1))

classifyInline :: Int -> ExceptT String Effect (Either Int Int)
classifyInline n
  | n < 0 = throwError ("negative " <> show n)
  | n `mod` 2 == 0 = pure (Left (n / 2))
  | otherwise = pure (Right (n * 3 + 1))

step :: Int -> ExceptT String Effect Int
step n = do
  c <- classify n
  liftEffect (log ("classified " <> show n))
  case c of
    Left half -> pure half
    Right next -> pure (next + 1)

stepInline :: Int -> ExceptT String Effect Int
stepInline n = do
  c <- classifyInline n
  case c of
    Left half -> pure (half - 1)
    Right next -> pure (next * 2)

passedOn :: Int -> ExceptT String Effect (Either Int Int)
passedOn n = do
  liftEffect (log ("passing on " <> show n))
  classify (n + 1)

main :: Effect Unit
main = do
  a <- runExceptT (step 304)
  log (show a)
  b <- runExceptT (step 207)
  log (show b)
  c <- runExceptT (step (-5))
  log (show c)
  d <- runExceptT (stepInline 8)
  log (show d)
  e <- runExceptT (stepInline 9)
  log (show e)
  f <- runExceptT (stepInline (-1))
  log (show f)
  g <- runExceptT (passedOn 41)
  log (show g)
  h <- runExceptT (passedOn (-3))
  log (show h)
