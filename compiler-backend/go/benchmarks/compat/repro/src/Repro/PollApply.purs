module Repro.PollApply where

import Prelude

import Control.Monad.ST.Class (liftST)
import Effect (Effect)
import Effect.Console (log)
import FRP.Event (subscribe)
import FRP.Event as Event
import FRP.Poll (Poll, sample_, step)

main :: Effect Unit
main = do
  clicks <- Event.create # liftST
  settings <- Event.create # liftST
  let doubled = (+) <$> step 1 settings.event <*> (pure 10 :: Poll Int)
  _ <- subscribe (sample_ doubled clicks.event) (\n -> log (show n)) # liftST
  clicks.push unit
  settings.push 5
  clicks.push unit
