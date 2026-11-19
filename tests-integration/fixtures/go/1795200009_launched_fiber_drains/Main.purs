module Main where

import Prelude

import Effect (Effect)
import Effect.Aff as Aff
import Effect.Class (liftEffect)
import Effect.Ref as Ref

-- | JavaScript's Aff runs a launched fiber, and every fiber it wakes on the way, until none can
-- run before `launchAff_` returns: joining a finished fiber resumes the parent at once.
main :: Effect Int
main = do
  steps <- Ref.new 0
  let step digit = Ref.modify_ (\steps' -> steps' * 10 + digit) steps
  Aff.launchAff_ do
    liftEffect (step 1)
    fiber <- Aff.forkAff (pure 2)
    joined <- Aff.joinFiber fiber
    liftEffect (step joined)
  step 3
  Ref.read steps
