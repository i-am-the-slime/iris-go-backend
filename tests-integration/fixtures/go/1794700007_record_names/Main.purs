module Main where

import Prelude

import Data.Foldable (foldl)
import Data.Maybe (Maybe(..), fromMaybe)
import Shapes as Shapes

-- A record is named after its synonym.
type Timing = { start :: Number, end :: Number }

-- A newtype names the record it wraps.
newtype Span = Span { from :: Int, to :: Int }

-- Each instantiation of a parameterised synonym is named after it, and
-- after its argument where they would collide.
type Pair a = { left :: a, right :: a }

duration :: Timing -> Number
duration timing = timing.end - timing.start

spanLength :: Array Span -> Int
spanLength = foldl (\acc (Span span) -> acc + span.to - span.from) 0

-- An anonymous record is named after the parameter it is passed in.
scaled :: Number -> Array { factor :: Number, offset :: Number } -> Number
scaled value adjustments = foldl (\acc adjustment -> acc * adjustment.factor + adjustment.offset) value adjustments

-- ... or after the field it sits in.
type Layout = { margins :: Array { top :: Number, bottom :: Number }, title :: String }

marginTotal :: Layout -> Number
marginTotal layout = foldl (\acc margin -> acc + margin.top + margin.bottom) 0.0 layout.margins

-- A data type applied to a record spells it by its name.
firstTimings :: Array (Maybe Timing) -> Number
firstTimings = foldl (\acc timing -> acc + fromMaybe 0.0 (map duration timing)) 0.0

sumPairs :: Array (Pair Int) -> Int
sumPairs = foldl (\acc pair -> acc + pair.left + pair.right) 0

joinPairs :: Array (Pair String) -> String
joinPairs = foldl (\acc pair -> acc <> pair.left <> pair.right) ""

main :: String
main = show
  [ duration { start: 1.0, end: 4.0 }
  , firstTimings [ Just { start: 2.0, end: 3.0 }, Nothing ]
  , scaled 2.0 [ { factor: 3.0, offset: 1.0 } ]
  , marginTotal { margins: [ { top: 1.0, bottom: 2.0 } ], title: "t" }
  , Shapes.area [ { width: 2.0, height: 3.0, label: "box" } ]
  ]
  <> show (spanLength [ Span { from: 2, to: 7 } ] + sumPairs [ { left: 1, right: 2 } ])
  <> joinPairs [ { left: "a", right: "b" } ]
