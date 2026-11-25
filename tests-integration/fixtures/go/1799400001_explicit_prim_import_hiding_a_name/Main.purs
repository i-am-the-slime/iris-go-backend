module Main where

import Prim hiding (Row)
import Prelude (Unit, show, (<>))

import Effect (Effect)
import Journal (log)

data Row = Row Int String

describe :: Row -> String
describe (Row number label) = label <> show number

main :: Effect Unit
main = log (describe (Row 1 "row "))
