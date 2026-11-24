module Main where

import Prelude

import Data.Maybe (Maybe(..))
import Effect (Effect)

newtype Policy m = Policy (Int -> m (Maybe Int))

type AnyPolicy = forall m. Monad m => Policy m

policy :: (Int -> Maybe Int) -> AnyPolicy
policy decide = Policy (pure <<< decide)

upTo :: Int -> Int -> Maybe Int
upTo limit n = if n >= limit then Nothing else Just (n * 10)

feed :: forall a b. a -> (a -> b) -> b
feed value use = use value

twice :: forall a b. (a -> a -> b) -> a -> b
twice use value = use value value

throughFeed :: Int -> AnyPolicy
throughFeed limit = feed (upTo limit) policy

throughFeedLambda :: Int -> AnyPolicy
throughFeedLambda limit = feed limit \bound -> policy (upTo bound)

throughTwice :: Int -> AnyPolicy
throughTwice limit = twice (\bound _ -> policy (upTo bound)) limit

decideWith :: forall m. Policy m -> Int -> m (Maybe Int)
decideWith (Policy decide) = decide

main :: Effect (Array String)
main = do
  fed <- decideWith (throughFeed 3) 2
  fedLambda <- decideWith (throughFeedLambda 3) 7
  doubled <- decideWith (throughTwice 4) 3
  pure [ show fed, show fedLambda, show doubled ]
