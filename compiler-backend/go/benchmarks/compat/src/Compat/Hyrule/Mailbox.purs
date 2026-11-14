module Compat.Hyrule.Mailbox where

import Prelude

import Control.Monad.ST.Class (liftST)
import Data.Foldable (for_)
import Effect (Effect)
import Effect.Console (log)
import FRP.Event (mailbox, mailboxed, subscribe)
import FRP.Event as Event

data Room = Kitchen | Garden | Attic

derive instance Eq Room
derive instance Ord Room

instance Show Room where
  show Kitchen = "kitchen"
  show Garden = "garden"
  show Attic = "attic"

main :: Effect Unit
main = do
  box <- mailbox # liftST
  _ <- subscribe (box.event Kitchen) (\s -> log ("kitchen got " <> s)) # liftST
  unsubscribeGarden <- subscribe (box.event Garden) (\s -> log ("garden got " <> s)) # liftST
  for_ [ Kitchen, Garden, Attic ] \room -> box.push { address: room, payload: "mail for " <> show room }
  unsubscribeGarden # liftST
  box.push { address: Garden, payload: "after unsubscribe" }
  letters <- Event.create # liftST
  _ <- subscribe (mailboxed letters.event \lookup -> lookup 3) (\inner -> void (subscribe inner (\b -> log ("three " <> show b)) # liftST)) # liftST
  letters.push { address: 1, payload: true }
  letters.push { address: 3, payload: false }
