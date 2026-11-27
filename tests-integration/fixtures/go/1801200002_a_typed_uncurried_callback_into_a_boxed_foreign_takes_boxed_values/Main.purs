module Main where

import Prelude

import Effect (Effect)
import Effect.Uncurried (mkEffectFn2)
import Pipe (leaked, newPipe, onTake)

type Spot = { x :: Int, y :: Int }

main :: Effect (Array String)
main = do
  let pipe = newPipe ({ x: 1, y: 2 } :: Spot)
  taken <- onTake pipe (mkEffectFn2 \{ x, y } open -> pure (show x <> "," <> show y <> " " <> show open))
  pure [ taken, show (leaked pipe) ]
