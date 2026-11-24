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

throughCompose :: Int -> AnyPolicy
throughCompose limit = (policy <<< upTo) limit

throughComposeFlipped :: Int -> AnyPolicy
throughComposeFlipped limit = (upTo >>> policy) limit

throughIdentity :: Int -> AnyPolicy
throughIdentity limit = identity (policy (upTo limit))

throughConst :: Int -> AnyPolicy
throughConst limit = const (policy (upTo limit)) "ignored"

decideWith :: forall m. Policy m -> Int -> m (Maybe Int)
decideWith (Policy decide) = decide

main :: Effect (Array String)
main = do
  composed <- decideWith (throughCompose 3) 2
  composedFlipped <- decideWith (throughComposeFlipped 3) 4
  identical <- decideWith (throughIdentity 3) 1
  constant <- decideWith (throughConst 3) 2
  pure [ show composed, show composedFlipped, show identical, show constant ]
