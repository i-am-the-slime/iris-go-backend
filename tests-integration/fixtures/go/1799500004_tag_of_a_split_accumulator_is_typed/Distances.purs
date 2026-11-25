module Distances where

import Prelude

data Distance = None | Distance Int Int Int Int Int Int

derive instance Eq Distance
derive instance Ord Distance

instance Show Distance where
  show None = "None"
  show (Distance a b c d e f) = "Distance " <> show [a, b, c, d, e, f]

measured :: Int -> Distance
measured n = if n < 0 then None else Distance n (n * 2) 0 1 n 3
