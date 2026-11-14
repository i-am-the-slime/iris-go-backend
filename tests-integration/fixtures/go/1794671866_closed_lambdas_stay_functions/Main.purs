module Main where

import Prelude

type Operation = { name :: String, run :: Int -> Int }

operations :: Int -> Array Operation
operations step =
  [ { name: "add", run: \x -> x + step }
  , { name: "scale", run: \x -> x * step }
  ]

applyAll :: Array Operation -> Int -> Int -> Int
applyAll ops index value = case ops of
  [ first, second ] -> if index == 0 then first.run value else second.run value
  _ -> value

main :: { added :: Int, scaled :: Int }
main =
  { added: applyAll (operations 3) 0 10
  , scaled: applyAll (operations 3) 1 10
  }
