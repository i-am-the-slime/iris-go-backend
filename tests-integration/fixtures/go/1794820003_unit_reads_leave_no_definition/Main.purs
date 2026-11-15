module Main where

import Prelude

import Data.Array as Array
import Data.Tuple (Tuple(..), fst, snd)
import Effect (Effect)
import Effect.Ref as Ref

check :: forall a. Eq a => { actual :: a, expected :: a } -> Effect Int
check { actual, expected } = pure (if actual == expected then 1 else 0)

units :: Array (Tuple Unit Unit)
units = [ Tuple unit unit, Tuple unit unit ]

main :: Effect Int
main = do
  actual <- pure unit
  same <- check { actual, expected: unit }
  count <- Ref.new 0
  Array.foldM (\_ pair -> Ref.modify_ (_ + 1) count *> pure (fst pair)) unit units
  counted <- Ref.read count
  let equal = Array.foldl (\total pair -> if fst pair == snd pair then total + 1 else total) 0 units
  pure (same * 100 + counted * 10 + equal)
