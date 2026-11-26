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

attempt :: Int -> Effect (Either Error (Either String Int))
attempt n = catchImpl (\failure -> pure (Left failure)) (Right <$> check n)

recovered :: Int -> Effect (Either String Int)
recovered n = catchImpl (\failure -> pure (Right (negate (codeOf failure)))) (check n)
  where
  codeOf failure = if message failure == "below zero" then 1 else 2

main :: Effect Unit
main = for_ [ 1, 3, -1 ] \n -> do
  result <- attempt n
  log case result of
    Left failure -> "threw " <> message failure
    Right (Left why) -> "failed " <> why
    Right (Right value) -> "got " <> show value
  fallback <- recovered n
  log (show fallback)
