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

throughApply :: Int -> AnyPolicy
throughApply limit = policy $ \n -> if n >= limit then Nothing else Just n

throughApplyFlipped :: Int -> AnyPolicy
throughApplyFlipped limit = upTo limit # policy

decideWith :: forall m. Policy m -> Int -> m (Maybe Int)
decideWith (Policy decide) = decide

main :: Effect (Array String)
main = do
  below <- decideWith (throughApply 3) 1
  above <- decideWith (throughApply 3) 5
  flipped <- decideWith (throughApplyFlipped 3) 2
  pure [ show below, show above, show flipped, show (decideWith (throughApply 2) 1 :: Maybe (Maybe Int)) ]
