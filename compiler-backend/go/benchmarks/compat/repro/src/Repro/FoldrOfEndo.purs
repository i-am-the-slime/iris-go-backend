module Repro.FoldrOfEndo where

import Prelude

import Data.Lens (toListOf, traversed)
import Effect (Effect)
import Effect.Console (log)

main :: Effect Unit
main = log (show (toListOf traversed [ 1, 2, 3 ]))
