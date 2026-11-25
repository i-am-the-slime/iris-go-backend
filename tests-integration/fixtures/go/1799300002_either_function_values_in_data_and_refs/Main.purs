module Main where

import Prelude

import Control.Monad.Error.Class (throwError)
import Control.Monad.Except (ExceptT, runExceptT)
import Effect (Effect)
import Effect.Class (liftEffect)
import Effect.Ref as Ref
import Journal (log)

data Step = Emit Int | Done

type Source = { name :: String, pull :: Unit -> ExceptT String Effect Step }

counter :: Int -> Effect Source
counter limit = do
  next <- Ref.new 0
  pure
    { name: "counter " <> show limit
    , pull: \_ -> do
        i <- liftEffect (Ref.read next)
        liftEffect (Ref.write (i + 1) next)
        if i == limit then throwError ("past " <> show limit)
        else pure (Emit i)
    }

taking :: Int -> Source -> Effect Source
taking n upstream = do
  left <- Ref.new n
  current <- Ref.new upstream.pull
  pure
    { name: upstream.name <> " taking " <> show n
    , pull: \_ -> do
        remaining <- liftEffect (Ref.read left)
        if remaining <= 0 then pure Done
        else do
          pull <- liftEffect (Ref.read current)
          step <- pull unit
          liftEffect (Ref.write (remaining - 1) left)
          pure step
    }

drain :: Source -> ExceptT String Effect Int
drain source = go 0
  where
  go total = do
    step <- source.pull unit
    case step of
      Emit x -> go (total + x)
      Done -> pure total

main :: Effect Unit
main = do
  short <- counter 10 >>= taking 4
  shortResult <- runExceptT (drain short)
  log (short.name <> ": " <> show shortResult)
  long <- counter 3 >>= taking 10
  longResult <- runExceptT (drain long)
  log (long.name <> ": " <> show longResult)
