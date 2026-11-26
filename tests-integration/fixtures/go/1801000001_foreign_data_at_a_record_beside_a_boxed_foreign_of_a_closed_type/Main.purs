module Main where

import Prelude

import Box (Box, get, put, sealed)
import Effect (Effect)

type Spot = { x :: Int, y :: Int }

type Room = { outbox :: Box Spot, seal :: Box Int }

main :: Effect (Array String)
main = pure (described room)
  where
  room = { outbox: put { x: 1, y: 2 }, seal: sealed "anything" } :: Room
  described { outbox, seal } = [ get outbox # spotted, get seal # show ]
  spotted { x, y } = show x <> "," <> show y
