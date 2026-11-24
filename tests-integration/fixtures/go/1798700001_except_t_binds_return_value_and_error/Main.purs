module Main where

import Prelude

import Control.Monad.Error.Class (catchError, throwError)
import Control.Monad.Except (ExceptT, runExceptT)
import Data.Either (Either(..))
import Data.Variant (Variant, inj, match)
import Effect (Effect)
import Effect.Class (liftEffect)
import Effect.Console (log)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Type.Proxy (Proxy(..))

type Failure = Variant (notFound :: String, tooBig :: Int)

lookupUser :: Int -> ExceptT Failure Effect String
lookupUser id
  | id == 42 = pure "Alice"
  | id > 1000 = throwError (inj (Proxy :: _ "tooBig") id)
  | otherwise = throwError (inj (Proxy :: _ "notFound") ("no user " <> show id))

greet :: Int -> ExceptT Failure Effect String
greet id = do
  name <- lookupUser id
  liftEffect (log ("found " <> name))
  friend <- lookupUser (id * 2 - id)
  pure ("hello " <> name <> " and " <> friend)

divide :: Int -> Int -> ExceptT String Effect Int
divide _ 0 = throwError "division by zero"
divide a b = pure (a / b)

chain :: Int -> ExceptT String Effect Int
chain n = do
  x <- divide 100 n
  y <- if x > 10 then divide x (n - 1) else pure x
  liftEffect (log ("chain " <> show x <> " " <> show y))
  pure (x + y)

countdown :: Int -> ExceptT String Effect Int
countdown n
  | n < 0 = throwError "below zero"
  | n == 0 = pure 0
  | otherwise = do
      rest <- countdown (n - 2)
      pure (rest + n)

status :: Int -> ExceptT Int Effect Int
status n
  | n > 100 = throwError 404
  | n > 3 = do
      next <- status (n * 2)
      pure (next + 1)
  | otherwise = pure 7

statuses :: Ref Int -> ExceptT Int Effect Int
statuses ref = do
  n <- liftEffect (Ref.modify (_ + 1) ref)
  a <- if n > 10 then throwError 500 else status n
  b <- if a > 5 then pure 1 else status (n + 4)
  pure (a + b)

describe :: Int -> ExceptT Failure Effect String
describe id = greet id `catchError` \failure -> pure (match { notFound: \message -> "missing: " <> message, tooBig: \n -> "too big: " <> show n } failure)

shown :: forall e. Either e String -> String
shown = case _ of
  Left _ -> "failed"
  Right text -> text

main :: Effect Unit
main = do
  r1 <- runExceptT (chain 5)
  log (show r1)
  r2 <- runExceptT (chain 0)
  log (show r2)
  r3 <- runExceptT (countdown 10)
  log (show r3)
  r4 <- runExceptT (countdown 9)
  log (show r4)
  a <- runExceptT (describe 42)
  log (shown a)
  b <- runExceptT (describe 7)
  log (shown b)
  c <- runExceptT (describe 5000)
  log (shown c)
  d <- runExceptT (greet 9)
  log (shown d)
  ref <- Ref.new 0
  s1 <- runExceptT (statuses ref)
  log (show s1)
  Ref.write 3 ref
  s2 <- runExceptT (statuses ref)
  log (show s2)
  Ref.write 19 ref
  s3 <- runExceptT (statuses ref)
  log (show s3)
