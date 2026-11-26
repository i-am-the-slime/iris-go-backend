module Main where

import Prelude

import Data.Typelevel.Num.Sets (class Nat, reifyInt, toInt)
import Effect (Effect)
import Effect.Console (log)

doubled :: forall n. Nat n => n -> Int
doubled n = toInt n * 2

described :: forall n. Nat n => n -> String
described n = "nat " <> show (toInt n)

main :: Effect Unit
main = do
  log (show ([ 0, 7, 10, 42, 905, 1234 ] <#> \wanted -> reifyInt wanted toInt))
  log (show (reifyInt 321 doubled))
  log (reifyInt 64 described)
