module Main where

import Prelude

import Control.Monad.Error.Class (throwError, try)
import Control.Monad.Except (ExceptT, runExceptT)
import Data.Either (Either(..))
import Data.Foldable (foldl)
import Effect (Effect)
import Journal (log)

status :: Int -> ExceptT Int Effect Int
status n
  | n > 100 = throwError n
  | otherwise = pure (n * 2)

tried :: Int -> ExceptT Int Effect Int
tried x = do
  r <- try (status x)
  case r of
    Left code -> pure (code + 1)
    Right doubled -> pure (doubled - 1)

sumUntilNegative :: Array Int -> Either Int Int
sumUntilNegative = foldl step (Right 0)
  where
  step total x = case total of
    Left bad -> Left bad
    Right sum
      | x < 0 -> Left x
      | otherwise -> Right (sum + x)

reassignedThenRead :: Int -> Either Int Int
reassignedThenRead n = do
  let first = if n > 0 then Right n else Left (-n)
  case first of
    Left bad -> Left (bad * 10)
    Right good -> if good > 5 then Left good else Right (good + 100)

main :: Effect Unit
main = do
  a <- runExceptT (tried 10)
  log (show a)
  b <- runExceptT (tried 500)
  log (show b)
  r <- runExceptT (status 50)
  case r of
    Left code -> log ("code " <> show code)
    Right value -> log ("value " <> show value)
  log (show (sumUntilNegative [ 1, 2, 3 ]))
  log (show (sumUntilNegative [ 1, -2, 3 ]))
  log (show (sumUntilNegative []))
  log (show (reassignedThenRead 3))
  log (show (reassignedThenRead 7))
  log (show (reassignedThenRead (-4)))
