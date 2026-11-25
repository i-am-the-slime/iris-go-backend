module Main where

import Prelude

import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Console (log)

newtype Policy m = Policy (Int -> m (Maybe Int))

type AnyPolicy = forall m. Monad m => Policy m

policy :: (Int -> Maybe Int) -> AnyPolicy
policy decide = Policy (pure <<< decide)

decideWith :: forall m. Policy m -> Int -> m (Maybe Int)
decideWith (Policy decide) = decide

main :: Effect Unit
main = do
  let limit = 3
  let below = policy $ \k -> if k > limit then Nothing else Just (k * 10)
  small <- decideWith below 2
  above <- decideWith capped 5
  log (show small <> " " <> show above)
  log (show (decideWith annotated 1 :: Maybe (Maybe Int)))
  shared <- decideWith annotated 7
  log (show shared)
  where
  capped = policy $ \k -> if k > 3 then Nothing else Just k
  annotated :: AnyPolicy
  annotated = policy $ \k -> Just (k + 1)
