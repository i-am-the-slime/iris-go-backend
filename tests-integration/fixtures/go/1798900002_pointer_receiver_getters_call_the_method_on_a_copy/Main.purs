module Main where

import Prelude

import Counter (Counter, bumped, count, zero)

type Held = { counter :: Counter, label :: String }

bumpedTwice :: Held -> Int
bumpedTwice held = bumped held.counter + bumped held.counter

countIfBumped :: Counter -> Int
countIfBumped counter = if bumped counter > 0 then count counter else -1

main :: Array Int
main =
  [ bumped zero
  , bumpedTwice { counter: zero, label: "held" }
  , countIfBumped zero
  , count zero
  ]
