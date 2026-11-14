module Compat.Hyrule.Basic where

import Prelude

import Control.Alt ((<|>))
import Control.Monad.ST.Class (liftST)
import Data.Filterable (filter)
import Data.Foldable (for_, traverse_)
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Console (log)
import FRP.Event (subscribe)
import FRP.Event as Event
import FRP.Event.Class (count, fold, withLast)

main :: Effect Unit
main = do
  numbers <- Event.create # liftST
  words <- Event.create # liftST
  let evens = filter (\n -> n `mod` 2 == 0) numbers.event
  let combined = map show evens <|> words.event
  let running = fold (+) 0 numbers.event
  unsubscribeCombined <- subscribe combined (\s -> log ("combined " <> s)) # liftST
  unsubscribeRunning <- subscribe running (\n -> log ("sum " <> show n)) # liftST
  unsubscribeCount <- subscribe (count words.event) (\n -> log ("words seen " <> show n)) # liftST
  unsubscribeLast <- subscribe (withLast numbers.event) describeLast # liftST
  for_ [ 1, 2, 3, 4 ] numbers.push
  traverse_ words.push [ "alpha", "beta" ]
  unsubscribeRunning # liftST
  numbers.push 10
  unsubscribeCombined # liftST
  unsubscribeCount # liftST
  unsubscribeLast # liftST
  numbers.push 12
  words.push "silent"
  log "done"
  where
  describeLast { now, last } = log case last of
    Nothing -> "first " <> show now
    Just previous -> "now " <> show now <> " after " <> show previous
