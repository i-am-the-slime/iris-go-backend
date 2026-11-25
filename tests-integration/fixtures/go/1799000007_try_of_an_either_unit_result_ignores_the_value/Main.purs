module Main where

import Prelude

import Control.Monad.Error.Class (throwError, try)
import Control.Monad.Except (ExceptT, runExceptT)
import Control.Monad.Reader (ReaderT, ask, runReaderT)
import Data.Either (Either(..))
import Data.Traversable (traverse)
import Effect (Effect)
import Effect.Class (liftEffect)
import Journal (log)

data Failure = Interrupted | Broken String | NoReply

instance Show Failure where
  show Interrupted = "Interrupted"
  show (Broken why) = "Broken " <> show why
  show NoReply = "NoReply"

isInterruption :: Failure -> Boolean
isInterruption = case _ of
  Interrupted -> true
  Broken why -> why == "interrupted"
  NoReply -> false

type App = ReaderT Int (ExceptT Failure Effect)

send :: Int -> App Unit
send n = do
  limit <- ask
  if n > limit then throwError Interrupted
  else if n < 0 then throwError (Broken "below zero")
  else if n == 0 then pure unit
  else do
    liftEffect (log ("sent " <> show n))
    send (n - 1)

type Client = { sendAll :: Int -> App Int }

client :: Int -> Client
client offset = { sendAll: \n -> do
    sent <- try (send n)
    case sent of
      Left failure | not (isInterruption failure) -> throwError failure
      _ -> pure unit
    reply <- liftEffect (receive n)
    case reply of
      Left failure -> throwError failure
      Right answer -> pure (answer * 2 + offset)
  }

receive :: Int -> Effect (Either Failure Int)
receive n = do
  log ("receiving " <> show n)
  pure (if n > 4 then Left NoReply else Right (n + 1))

main :: Effect Unit
main = do
  results <- traverse (\{ sendAll } -> traverse (\n -> runExceptT (runReaderT (sendAll n) 3)) [ 2, 5, -1 ]) [ client 100, client 200 ]
  log (show results)
