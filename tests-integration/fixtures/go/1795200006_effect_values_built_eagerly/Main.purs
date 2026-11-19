module Main where

import Prelude

import Data.Either (either)
import Effect (Effect)
import Effect.Exception as Exception
import Effect.Ref as Ref
import Partial.Unsafe (unsafeCrashWith)

-- | JavaScript evaluates the value `pure` holds while building the effect, so the crash happens
-- before `try` can catch it.
main :: Effect Int
main = do
  steps <- Ref.new 1
  caught <- Exception.try (pure (if true then unsafeCrashWith "boom" else 1))
  Ref.modify_ (_ * 10) steps
  Ref.modify_ (_ + either (const 1) identity caught) steps
  Ref.read steps
