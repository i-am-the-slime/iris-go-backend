module Compat.Hyrule.Fix where

import Prelude

import Control.Alt ((<|>))
import Control.Monad.ST.Class (liftST)
import Control.Monad.ST.Internal as STRef
import Data.Foldable (for_)
import Effect (Effect)
import Effect.Console (log)
import FRP.Event (foldE, foldST, memoize, subscribe)
import FRP.Event as Event
import FRP.Event.Class (fix, sampleOnRight)

main :: Effect Unit
main = do
  ticks <- Event.create # liftST
  let accumulated = fix \previous -> sampleOnRight (previous <|> map (const 0) ticks.event) (map (\n acc -> acc + n) ticks.event)
  _ <- subscribe (foldE (\acc n -> pure (acc * 2 + n)) 1 ticks.event) (\n -> log ("foldE " <> show n)) # liftST
  _ <- subscribe (foldST (\acc n -> pure (acc <> show n)) "" ticks.event) (\s -> log ("foldST " <> s)) # liftST
  _ <- subscribe accumulated (\n -> log ("fix " <> show n)) # liftST
  pushes <- STRef.new 0 # liftST
  memoized <- memoize (map (_ * 3) ticks.event) # liftST
  _ <- subscribe memoized.event (\n -> log ("memo a " <> show n)) # liftST
  _ <- subscribe memoized.event (\n -> do
    _ <- STRef.modify (_ + 1) pushes # liftST
    log ("memo b " <> show n)) # liftST
  for_ [ 1, 2, 3 ] ticks.push
  memoized.unsubscribe # liftST
  ticks.push 4
  total <- STRef.read pushes # liftST
  log ("memo b ran " <> show total)
