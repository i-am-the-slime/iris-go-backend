module Repro.DiscardedEffectResult where

import Prelude

import Effect (Effect)
import Effect.Console (log)
import Effect.Ref as Ref
import Data.Foldable as Data.Foldable

type Subscribe = (Int -> Effect Unit) -> Effect (Effect Unit)

create :: Effect { subscribe :: Subscribe, push :: Int -> Effect Unit }
create = do
  subscribers <- Ref.new []
  pure
    { subscribe: \k -> do
        Ref.modify_ (_ <> [ k ]) subscribers
        pure (pure unit)
    , push: \n -> Ref.read subscribers >>= Data.Foldable.traverse_ \k -> k n
    }

-- | Like hyrule's `sampleOnRight`: remembers the left's latest value and emits on the right.
both :: Subscribe -> Subscribe -> Subscribe
both left right k = do
  latest <- Ref.new 0
  c1 <- left \n -> Ref.write n latest
  c2 <- right \n -> Ref.read latest >>= \previous -> k (previous + n)
  pure (c1 *> c2)

-- | Like hyrule's `fix`: subscribes to a fresh channel and returns only the second canceller.
fix :: (Subscribe -> Subscribe) -> Subscribe
fix f k = do
  { subscribe, push } <- create
  _ <- subscribe k
  c <- f subscribe push
  pure c

main :: Effect Unit
main = do
  ticks <- create
  _ <- fix (\previous -> both previous ticks.subscribe) (\n -> log (show n))
  ticks.push 1
