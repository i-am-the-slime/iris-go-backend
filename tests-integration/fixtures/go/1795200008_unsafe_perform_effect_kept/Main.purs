module Main where

import Prelude

import Control.Monad.ST as ST
import Data.Array.ST as STArray
import Data.Function (applyN)
import Data.Maybe (Maybe(..), maybe)
import Effect (Effect)
import Effect.Ref as Ref
import Effect.Unsafe (unsafePerformEffect)

constantly :: forall a. a -> Int
constantly _ = 0

-- | The effects run where JavaScript evaluates their arguments: a `show` of the Unit result, an
-- unused binding, a function argument the array operation never calls, and an argument that a
-- function ignores, computed by a local function.
main :: Effect Int
main = do
  count <- Ref.new 0
  let bump = unsafePerformEffect (Ref.modify_ (_ + 1) count)
  let shown = show (unsafePerformEffect (Ref.modify_ (_ + 10) count))
  let chosen = applyN (\_ -> unit) 0 (maybe unit (\_ -> unsafePerformEffect (Ref.modify_ (_ + 100) count)) (Just 1))
  let modified = ST.run do
        array <- STArray.new
        STArray.modify 0 (unsafePerformEffect (Ref.modify_ (_ + 1000) count *> pure identity)) array
  let
    tick :: Int -> Int
    tick value = unsafePerformEffect (Ref.modify_ (_ + 10000) count *> pure value)
  let ignored = constantly (tick 1)
  total <- Ref.read count
  pure (ignored + total + (if modified then 1 else 0) + (if shown == "unit" then 0 else 1))
