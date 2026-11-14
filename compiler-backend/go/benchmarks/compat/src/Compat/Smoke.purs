module Compat.Smoke where

import Prelude

import Effect (Effect)
import Effect.Console (log)

main :: Effect Unit
main = log (show (map (_ * 2) [ 1, 2, 3 ]))
