module Lib.Json.Extra where

import Prelude

import Lib.JSON (doubled)

tripled :: Int -> Int -> Int
tripled total n = if n <= 0 then total else tripled (total + doubled 0 1 + 1) (n - 1)
