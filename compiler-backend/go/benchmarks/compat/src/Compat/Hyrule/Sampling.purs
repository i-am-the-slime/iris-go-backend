module Compat.Hyrule.Sampling where

import Prelude

import Control.Monad.ST.Class (liftST)
import Data.Foldable (for_)
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Effect.Console (log)
import FRP.Event (Event, subscribe)
import FRP.Event as Event
import FRP.Event.Class (gate, keepLatest, mapAccum, sampleOnLeft, sampleOnRight)

main :: Effect Unit
main = do
  values <- Event.create # liftST
  functions <- Event.create # liftST
  gates <- Event.create # liftST
  outer <- Event.create # liftST
  innerA <- Event.create # liftST
  innerB <- Event.create # liftST
  _ <- subscribe (sampleOnRight values.event functions.event) (\n -> log ("right " <> show n)) # liftST
  _ <- subscribe (sampleOnLeft values.event functions.event) (\n -> log ("left " <> show n)) # liftST
  _ <- subscribe (gate gates.event values.event) (\n -> log ("gated " <> show n)) # liftST
  _ <- subscribe (numbered values.event) (\s -> log s) # liftST
  _ <- subscribe (keepLatest outer.event) (\s -> log ("latest " <> s)) # liftST
  values.push 1
  functions.push (_ * 10)
  values.push 2
  functions.push (_ + 100)
  gates.push true
  values.push 3
  gates.push false
  values.push 4
  outer.push innerA.event
  innerA.push "a1"
  outer.push innerB.event
  innerA.push "a2"
  innerB.push "b1"
  for_ [ 5, 6 ] values.push
  where
  numbered :: Event Int -> Event String
  numbered = mapAccum (\index value -> (index + 1) /\ (show index <> ":" <> show value)) 0
