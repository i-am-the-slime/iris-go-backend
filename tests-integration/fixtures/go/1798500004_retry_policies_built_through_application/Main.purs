module Main where

import Prelude

import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Ref as Ref

newtype RetryStatus = RetryStatus { iterNumber :: Int, cumulativeDelay :: Number }

newtype RetryPolicyM m = RetryPolicyM (RetryStatus -> m (Maybe Number))

type RetryPolicy = forall m. Monad m => RetryPolicyM m

instance Monad m => Semigroup (RetryPolicyM m) where
  append (RetryPolicyM first) (RetryPolicyM second) = RetryPolicyM \status -> do
    left <- first status
    right <- second status
    pure (max <$> left <*> right)

retryPolicy :: (RetryStatus -> Maybe Number) -> RetryPolicy
retryPolicy decide = RetryPolicyM (pure <<< decide)

limitRetries :: Int -> RetryPolicy
limitRetries limit = retryPolicy $ \(RetryStatus { iterNumber }) ->
  if iterNumber >= limit then Nothing else Just 0.0

constantDelay :: Number -> RetryPolicy
constantDelay delay = retryPolicy <<< const <<< pure $ delay

retrying :: RetryPolicyM Effect -> (RetryStatus -> Effect Boolean) -> Effect RetryStatus
retrying (RetryPolicyM decide) action = go (RetryStatus { iterNumber: 0, cumulativeDelay: 0.0 })
  where
  go status@(RetryStatus { iterNumber, cumulativeDelay }) = do
    succeeded <- action status
    if succeeded then pure status
    else decide status >>= case _ of
      Nothing -> pure status
      Just delay -> go (RetryStatus { iterNumber: iterNumber + 1, cumulativeDelay: cumulativeDelay + delay })

describe :: RetryStatus -> String
describe (RetryStatus { iterNumber, cumulativeDelay }) =
  "stopped after " <> show iterNumber <> " retries, waiting " <> show cumulativeDelay

main :: Effect (Array String)
main = do
  attempts <- Ref.new 0
  let succeedOnThird _ = Ref.modify (_ + 1) attempts <#> (_ >= 3)
  recovered <- retrying (constantDelay 50.0 <> limitRetries 5) succeedOnThird
  exhausted <- retrying (limitRetries 2) (\_ -> pure false)
  delayed <- retrying (constantDelay 10.0 <> limitRetries 4) (\_ -> pure false)
  pure [ describe recovered, describe exhausted, describe delayed ]
