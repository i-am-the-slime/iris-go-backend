module Main where

import Prelude

data Expr = Val Int | Add Expr Expr | Mul Expr Expr | Sub Expr Expr

data Shape
  = Circle Number
  | Square Number
  | Label String Boolean
  | Caption String Boolean
  | Point

data Item = Field String | Pair Int Int | Couple Int Int

data Colour = Red | Green | Blue

data Sample = Sample Boolean Number Int String

evaluate :: Expr -> Int
evaluate (Val value) = value
evaluate (Add left right) = evaluate left + evaluate right
evaluate (Mul left right) = evaluate left * evaluate right
evaluate (Sub left right) = evaluate left - evaluate right

describe :: Shape -> String
describe (Circle radius) = "circle " <> show radius
describe (Square side) = "square " <> show side
describe (Label text bold) = "label " <> text <> show bold
describe (Caption text bold) = "caption " <> text <> show bold
describe Point = "point"

itemTotal :: Item -> Int
itemTotal (Field _) = 0
itemTotal (Pair left right) = left + right
itemTotal (Couple left right) = left * right

colourName :: Colour -> String
colourName Red = "red"
colourName Green = "green"
colourName Blue = "blue"

sampleText :: Sample -> String
sampleText (Sample flag ratio count name) = name <> show flag <> show ratio <> show count

main
  :: { expression :: Int
     , shapes :: Array String
     , items :: Array Int
     , colours :: Array String
     , sample :: String
     }
main =
  { expression: evaluate (Add (Val 1) (Sub (Mul (Val 2) (Val 3)) (Val 4)))
  , shapes: map describe [ Circle 1.0, Square 2.0, Label "a" true, Caption "b" false, Point ]
  , items: map itemTotal [ Field "x", Pair 1 2, Couple 3 4 ]
  , colours: map colourName [ Red, Green, Blue ]
  , sample: sampleText (Sample true 0.5 3 "s")
  }
