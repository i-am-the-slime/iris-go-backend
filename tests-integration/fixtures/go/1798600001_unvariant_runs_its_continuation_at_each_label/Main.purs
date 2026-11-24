module Main where

import Prelude

import Data.Symbol (reflectSymbol)
import Data.Variant (Unvariant(..), Variant, inj, match, revariant, unvariant)
import Type.Proxy (Proxy(..))

type Shape = Variant (circle :: Number, square :: Int, caption :: String)

shapes :: Array Shape
shapes =
  [ inj (Proxy @"circle") 1.5
  , inj (Proxy @"square") 2
  , inj (Proxy @"caption") "hi"
  ]

labelOf :: forall r. Variant r -> String
labelOf variant = case unvariant variant of
  Unvariant run -> run \label _ -> reflectSymbol label

labelLength :: forall r. Variant r -> Int
labelLength variant = case unvariant variant of
  Unvariant run -> run \label _ -> stringLength (reflectSymbol label)
  where
  stringLength = case _ of
    "circle" -> 6
    "square" -> 6
    _ -> 0

describe :: Shape -> String
describe = match
  { circle: \radius -> "circle " <> show radius
  , square: \side -> "square " <> show side
  , caption: \text -> "caption " <> text
  }

roundTrip :: Shape -> Shape
roundTrip = revariant <<< unvariant

main :: Array String
main =
  [ show (map labelOf shapes)
  , show (map labelLength shapes)
  , show (map (describe <<< roundTrip) shapes)
  , show (map (labelOf <<< roundTrip <<< roundTrip) shapes)
  , labelOf (inj (Proxy @"only") unit :: Variant (only :: Unit))
  ]
