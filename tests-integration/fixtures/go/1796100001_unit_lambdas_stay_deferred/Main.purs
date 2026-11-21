module Main where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl, for_)
import Actions (runWhenAsked)
import Effect (Effect)
import Effect.Exception (throw)

-- | A value worked out only when it is forced.
newtype Later a = Later (Unit -> a)

defer :: forall a. (Unit -> a) -> Later a
defer = Later

force :: forall a. Later a -> a
force (Later later) = later unit

expensive :: Int -> Int
expensive n = foldl (+) 0 (Array.range 1 n)

-- | `expensive n` is worked out when the `Later` is forced, not when it is built.
deferred :: Int -> Later Int
deferred n = defer \_ -> expensive n

-- | `f x` is worked out when the action runs, not when it is built: `runWhenAsked` gets a
-- | function that works it out.
later :: forall a b. (a -> Effect b) -> a -> Effect b
later f x = pure unit >>= \_ -> f x

-- | A thunk whose body does no work leaves nothing to wait for, so its bind goes.
answer :: Effect Int
answer = pure unit >>= \_ -> pure 42

-- | `map` calls its callback right there, so the callback is no thunk and runs in the loop.
shifted :: Int -> Array Int -> Array Int
shifted n = map \x -> x + expensive n

-- | A do block's binds are no thunks the source writes: `pure` there binds `total` in the loop.
checked :: Int -> Array Int -> Effect Unit
checked n xs = for_ xs \x -> do
  total <- pure (x + expensive n)
  when (total < 0) (throw "negative")

main :: Effect Unit
main = do
  let laters = map deferred [ 100, 10 ]
  when (map force laters /= [ 5050, 55 ]) do
    throw "the deferred values are wrong"
  bound <- runWhenAsked (later (\n -> pure (expensive n)) 10)
  mapped <- runWhenAsked (map (\_ -> expensive 20) (pure unit))
  free <- runWhenAsked answer
  when ([ bound, mapped, free ] /= [ 55, 210, 42 ]) do
    throw "the continued values are wrong"
  when (shifted 10 [ 1, 2 ] <> shifted 4 [ 1 ] /= [ 56, 57, 11 ]) do
    throw "the shifted values are wrong"
  checked 10 [ 1, 2 ]
  checked 4 [ 1, 2 ]
