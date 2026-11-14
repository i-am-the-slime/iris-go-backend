module Main where

import Prelude

import Data.Foldable (traverse_)
import Effect (Effect)
import Effect.Ref as Ref

type Subscribe = (Int -> Effect Unit) -> Effect (Effect Unit)

create :: Effect { subscribe :: Subscribe, push :: Int -> Effect Unit }
create = do
  subscribers <- Ref.new []
  pure
    { subscribe: \k -> do
        Ref.modify_ (_ <> [ k ]) subscribers
        pure (pure unit)
    , push: \n -> Ref.read subscribers >>= traverse_ \k -> k n
    }

sampleOnRight :: Subscribe -> Subscribe -> Subscribe
sampleOnRight left right k = do
  latest <- Ref.new 0
  c1 <- left \n -> Ref.write n latest
  c2 <- right \n -> Ref.read latest >>= \previous -> k (previous + n)
  pure (c1 *> c2)

-- | The cancellers `c1` and `c2` reach only the result of `fix`, which `main` discards.
fix :: (Subscribe -> Subscribe) -> Subscribe
fix f k = do
  { subscribe, push } <- create
  _ <- subscribe k
  c <- f subscribe push
  pure c

main :: Effect Int
main = do
  total <- Ref.new 0
  ticks <- create
  _ <- fix (\previous -> sampleOnRight previous ticks.subscribe) (\n -> Ref.modify_ (_ + n) total)
  ticks.push 1
  ticks.push 2
  Ref.read total
