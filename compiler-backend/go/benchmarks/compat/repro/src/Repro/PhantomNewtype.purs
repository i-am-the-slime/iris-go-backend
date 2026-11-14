module Repro.PhantomNewtype where

import Prelude

import Effect (Effect)
import Effect.Console (log)

newtype Distance (unit :: Type) = Distance Number
data Metres
data Feet

metres :: Number -> Distance Metres
metres = Distance

toFeet :: Distance Metres -> Distance Feet
toFeet (Distance m) = Distance (m * 3.28084)

main :: Effect Unit
main = log (case toFeet (metres 10.0) of Distance feet -> show feet)
