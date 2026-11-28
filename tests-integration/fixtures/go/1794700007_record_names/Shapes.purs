module Shapes where

import Prelude

import Data.Foldable (foldl)

-- Another module's `Timing` takes the same name only in another package.
type Timing = { width :: Number, height :: Number, label :: String }

area :: Array Timing -> Number
area = foldl (\acc shape -> acc + shape.width * shape.height) 0.0
