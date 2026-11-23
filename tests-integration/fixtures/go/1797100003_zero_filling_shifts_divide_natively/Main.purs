module Main where

import Prelude

import Data.Foldable (for_)
import Data.Int.Bits (zshr)
import Effect (Effect)
import Effect.Ref as Ref

bucket :: Int -> Int
bucket x = (x `zshr` 1) `mod` 10

eighth :: Int -> Int
eighth x = (x `zshr` 3) / 7

unshifted :: Int -> Int
unshifted x = (x `zshr` 0) `mod` 10

main :: Effect Unit
main = do
  output <- Ref.new []
  inputs <- Ref.new [ -7, 123457, -1, 0 ]
  values <- Ref.read inputs
  for_ values \x -> Ref.modify_ (_ <> [ bucket x, eighth x, unshifted x ]) output
  void (Ref.read output)
