module Main where

import Prelude

import Effect (Effect)
import Effect.Exception (throw)
import Effect.Ref as Ref

main :: Effect Unit
main = do
  count <- Ref.new 0
  Ref.modify_ (_ + 1) count
  seen <- Ref.read count
  when (seen > 0) (throw "boom")
