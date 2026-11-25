module Main where

import Prelude

import Data.Array ((..))
import Data.Foldable (for_)
import Effect (Effect)
import Effect.Exception (throw)
import Effect.Ref as Ref

type Rule = { name :: String, check :: Int -> Boolean }

rules :: Int -> Array Rule
rules limit =
  [ { name: "positive", check: \n -> n > 0 }
  , { name: "small", check: \n -> n < limit }
  , { name: "even", check: \n -> n `mod` 2 == 0 }
  ]

main :: Effect Unit
main = do
  passed <- Ref.new 0
  limit <- Ref.new 3 >>= Ref.read
  for_ (0 .. 4) \n ->
    for_ (rules limit) \rule ->
      when (rule.check n) do
        Ref.modify_ (_ + 1) passed
  total <- Ref.read passed
  when (total /= 10) do
    throw ("the rules passed " <> show total)
