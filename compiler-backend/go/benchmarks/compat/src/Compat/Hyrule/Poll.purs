module Compat.Hyrule.Poll where

import Prelude

import Control.Monad.ST.Class (liftST)
import Data.Foldable (for_)
import Effect (Effect)
import Effect.Console (log)
import FRP.Event (subscribe)
import FRP.Event as Event
import FRP.Poll (Poll, sample_, sham, step, switcher)
import FRP.Poll as Poll

main :: Effect Unit
main = do
  clicks <- Event.create # liftST
  settings <- Event.create # liftST
  polls <- Event.create # liftST
  let temperature = step 20 settings.event :: Poll Int
  let doubled = map (_ * 2) temperature + pure 1
  let switched = switcher (pure 0) polls.event
  _ <- subscribe (sample_ doubled clicks.event) (\n -> log ("doubled " <> show n)) # liftST
  _ <- subscribe (sample_ switched clicks.event) (\n -> log ("switched " <> show n)) # liftST
  _ <- subscribe (Poll.sample (sham settings.event) (map (\c t -> c <> show t) clicks.event)) (\s -> log ("sham " <> s)) # liftST
  clicks.push "a"
  settings.push 25
  clicks.push "b"
  polls.push temperature
  clicks.push "c"
  polls.push (pure 7)
  for_ [ "d", "e" ] clicks.push
