module Main where

import Prelude

import Control.Monad.Error.Class (throwError)
import Control.Monad.Except (ExceptT, runExceptT)
import Data.Either (Either(..))
import Effect (Effect)
import Effect.Class (liftEffect)
import Journal (log)

data Problem = Negative Int | TooLarge Int

instance Show Problem where
  show (Negative n) = "Negative " <> show n
  show (TooLarge n) = "TooLarge " <> show n

check :: Int -> ExceptT Problem Effect Int
check n
  | n < 0 = throwError (Negative n)
  | n > 1000 = throwError (TooLarge n)
  | otherwise = pure (n * 3)

settle :: String -> Either Problem Int -> Effect String
settle label outcome = case outcome of
  Left (Negative n) -> do
    log (label <> ": below zero by " <> show (negate n))
    pure "negative"
  Left problem -> do
    log (label <> ": " <> show problem)
    pure "failed"
  Right value
    | value > 100 -> settle (label <> " again") (Left (TooLarge value))
    | otherwise -> do
        log (label <> ": " <> show value)
        pure "ok"

run :: Int -> Effect String
run n = do
  outcome <- runExceptT (check n)
  settle ("run " <> show n) outcome

kept :: Int -> ExceptT Problem Effect Int
kept n = do
  a <- check n
  liftEffect (log ("checked " <> show a))
  b <- check (a - 50)
  pure (a + b)

main :: Effect Unit
main = do
  r1 <- run 5
  log r1
  r2 <- run (-2)
  log r2
  r3 <- run 2000
  log r3
  r4 <- run 40
  log r4
  r5 <- runExceptT (kept 30)
  case r5 of
    Left problem -> settle "kept" (Left problem) >>= log
    Right value -> settle "kept" (Right value) >>= log
  r6 <- runExceptT (kept 2)
  log (show r6)
