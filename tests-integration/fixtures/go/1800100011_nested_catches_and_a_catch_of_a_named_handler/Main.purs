module Main where

import Prelude

import Data.Either (Either(..))
import Data.Foldable (for_)
import Effect (Effect)
import Effect.Exception (Error, message, throw)
import Go.IO.Internal (catchImpl)
import Journal (log)

check :: Int -> Effect (Either String Int)
check n
  | n > 2 = pure (Left ("too many: " <> show n))
  | n < 0 = throw "below zero"
  | otherwise = pure (Right (n * 10))

retried :: Int -> Effect (Either Error (Either String Int))
retried n = catchImpl (\failure -> pure (Left failure)) do
  first <- catchImpl (\_ -> check (negate n)) (check n)
  case first of
    Left why | why == "too many: 3" -> throw "gave up"
    _ -> pure (Right first)

reportFailure :: Error -> Effect (Either String Int)
reportFailure failure = do
  log ("reported " <> message failure)
  pure (Left (message failure))

reported :: Int -> Effect (Either String Int)
reported n = catchImpl reportFailure (check n)

main :: Effect Unit
main = for_ [ 1, 3, -1, -4 ] \n -> do
  result <- retried n
  log case result of
    Left failure -> "threw " <> message failure
    Right (Left why) -> "failed " <> why
    Right (Right value) -> "got " <> show value
  outcome <- reported n
  log (show outcome)
