module Main where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Variant (Variant, case_, expand, inj, on, over, overSome, traverse)
import Effect (Effect)
import Journal (log)
import Type.Proxy (Proxy(..))

type Shape = Variant (circle :: Int, square :: Number)

describe :: Shape -> String
describe = case_ # on (Proxy @"circle") (\radius -> "circle " <> show radius) # on (Proxy @"square") (\side -> "square " <> show side)

main :: Effect Unit
main = do
  let circle = inj (Proxy @"circle") 21 :: Shape
  let square = inj (Proxy @"square") 1.5 :: Shape
  log (describe (over { circle: (_ * 2) } circle))
  log (describe (overSome { square: (_ * 2.0) } expand square))
  log (show (map describe (traverse { circle: \radius -> Just (radius + 1) } circle :: Maybe Shape)))
