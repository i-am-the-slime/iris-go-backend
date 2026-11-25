module Main where

import Prelude

import Data.Maybe (Maybe(..))

newtype Policy m = Policy (Int -> m (Maybe Int))

type AnyPolicy = forall m. Monad m => Policy m

policy :: (Int -> Maybe Int) -> AnyPolicy
policy decide = Policy (pure <<< decide)

decideWith :: forall m. Policy m -> Int -> m (Maybe Int)
decideWith (Policy decide) = decide

main :: Array String
main = do
  let below = policy $ \k -> if k > 3 then Nothing else Just (k * 10)
  map show (decideWith capped 5 <> decideWith below 2)
  where
  capped = policy $ \k -> if k > 3 then Nothing else Just k
