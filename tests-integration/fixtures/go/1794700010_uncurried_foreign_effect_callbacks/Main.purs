module Main where

import Prelude

import Data.Array as Array
import Effect (Effect)
import Effect.Ref as Ref

main :: Effect Int
main = do
  seen <- Ref.new 0
  total <- Array.foldM (\acc n -> Ref.modify_ (_ + 1) seen $> (acc + n)) 0 [ 1, 2, 3 ]
  count <- Ref.read seen
  pure (total * 10 + count)
