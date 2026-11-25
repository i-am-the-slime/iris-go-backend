module Lib.JSON where

import Prelude

doubled :: Int -> Int -> Int
doubled total n = if n <= 0 then total else doubled (total + 2) (n - 1)
