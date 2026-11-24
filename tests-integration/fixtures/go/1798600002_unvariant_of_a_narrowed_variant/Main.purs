module Main where

import Prelude

import Data.Maybe (Maybe)
import Data.Symbol (reflectSymbol)
import Data.Variant (Unvariant(..), Variant, contract, inj, on, revariant, unvariant)
import Type.Proxy (Proxy(..))

type Shape = Variant (circle :: Number, square :: Int, caption :: String)

type Corners = Variant (square :: Int, caption :: String)

shapes :: Array Shape
shapes =
  [ inj (Proxy @"circle") 1.5
  , inj (Proxy @"square") 2
  , inj (Proxy @"caption") "hi"
  ]

labelOf :: forall r. Variant r -> String
labelOf variant = case unvariant variant of
  Unvariant run -> run \label _ -> reflectSymbol label

cornered :: Shape -> Maybe Corners
cornered = contract

roundTripped :: Shape -> String
roundTripped = on (Proxy @"square") (\side -> "side " <> show side) (labelOf <<< revariant <<< unvariant)

main :: Array String
main =
  [ show (map (map labelOf <<< cornered) shapes)
  , show (map labelOf shapes)
  , show (map roundTripped shapes)
  ]
