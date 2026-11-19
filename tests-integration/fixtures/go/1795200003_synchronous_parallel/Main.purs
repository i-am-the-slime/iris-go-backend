module Main where

import Prelude

import Control.Parallel (parSequence, parTraverse, parallel, sequential)
import Data.Foldable (sum)
import Data.Time.Duration (Milliseconds(..))
import Effect (Effect)
import Effect.Aff (Aff, delay, launchAff_)

squares :: Int -> Aff (Array Int)
squares n = parTraverse (\i -> pure (i * i)) [ 1, 2, n ]

paused :: Int -> Aff (Array Int)
paused n = parTraverse (\i -> delay (Milliseconds 1.0) *> pure (i + n)) [ 1, 2 ]

paired :: Int -> Aff Int
paired n = sequential ((+) <$> parallel (pure n) <*> parallel (pure (n * 2)))

counted :: Int -> Aff (Array Int)
counted n = parSequence [ pure n, pure (n + 1) ]

main :: Effect Unit
main = launchAff_ do
  xs <- squares 3
  ys <- paused 10
  z <- paired 4
  _ <- counted (sum xs + sum ys + z)
  pure unit
