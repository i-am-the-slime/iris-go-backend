module Main where

import Prelude

import Data.Variant (Variant, case_, default, expand, inj, match, on, onMatch)
import Type.Proxy (Proxy(..))

opaque :: Int -> Int
opaque x = if x == 12345 then opaque x else x

type Shape = Variant (circle :: Number, square :: Int)

type Named = Variant (circle :: Number, square :: Int, label :: String)

shape :: Int -> Shape
shape n = if n > 0 then inj (Proxy :: Proxy "circle") 1.5 else inj (Proxy :: Proxy "square") n

area :: Shape -> Number
area = case_
  # on (Proxy :: Proxy "circle") (\r -> r * r)
  # on (Proxy :: Proxy "square") (\s -> toNumber (s * s))
  where
  toNumber :: Int -> Number
  toNumber s = if s > 0 then 4.0 else 0.0

describe :: Named -> String
describe = match
  { circle: \r -> "circle " <> show r
  , square: \s -> "square " <> show s
  , label: \l -> l
  }

labelOnly :: Named -> String
labelOnly = default "a shape" # onMatch { label: \l -> "label " <> l }

widen :: Shape -> Named
widen = expand

main :: Array String
main =
  [ show (area (shape (opaque 1)))
  , show (area (shape (opaque (-2))))
  , describe (widen (shape (opaque 3)))
  , describe (inj (Proxy :: Proxy "label") "tag")
  , labelOnly (widen (shape (opaque 0)))
  , labelOnly (inj (Proxy :: Proxy "label") "x")
  ]
