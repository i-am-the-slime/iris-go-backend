module Repro.ExistsShowBox where

import Prelude

import Data.Exists (Exists, mkExists, runExists)
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Console (log)

data ShowBoxF a = ShowBoxF a (a -> String)

box :: forall a. Show a => a -> Exists ShowBoxF
box a = mkExists (ShowBoxF a show)

render :: Exists ShowBoxF -> String
render = runExists \(ShowBoxF a f) -> f a

main :: Effect Unit
main = log (show (map render [ box 1, box "two", box [ 3.0 ], box (Just true) ]))
