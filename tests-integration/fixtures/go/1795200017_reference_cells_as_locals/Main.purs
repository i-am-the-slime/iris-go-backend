module Main where

import Prelude

import Control.Monad.ST (ST, for, run, while)
import Control.Monad.ST.Ref (STRef)
import Control.Monad.ST.Ref as STRef
import Data.Foldable (for_)
import Effect (Effect)
import Effect.Ref (Ref)
import Effect.Ref as Ref

counted :: Int -> Int
counted n = run do
  total <- STRef.new 0
  index <- STRef.new 0
  while (map (_ < n) (STRef.read index)) do
    i <- STRef.read index
    _ <- STRef.modify (_ + i) total
    void (STRef.write (i + 1) index)
  for 0 n \i -> void (STRef.modify (_ + i) total)
  STRef.read total

summed :: Array Int -> Int
summed numbers = run do
  total <- STRef.new 0
  for_ numbers \x -> addTo total x
  STRef.read total
  where
  addTo :: forall region. STRef region Int -> Int -> ST region Unit
  addTo cell x = void (STRef.modify (_ + x) cell)

drained :: Int -> Effect Int
drained n = do
  hits <- Ref.new 0
  drain hits n
  Ref.read hits

drain :: Ref Int -> Int -> Effect Unit
drain cell n
  | n <= 0 = pure unit
  | otherwise = do
      Ref.modify_ (_ + n) cell
      drain cell (n - 1)

main :: Effect Int
main = do
  hits <- drained 3
  pure (counted 4 + summed [ 1, 2 ] + hits)
