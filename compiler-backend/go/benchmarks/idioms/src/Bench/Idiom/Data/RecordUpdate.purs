module Bench.Idiom.Data.RecordUpdate where

import Prelude

import Bench.Harness (benchmark)
import Data.Array as Array
import Data.Foldable (foldl)
import Effect (Effect)

idiom :: String
idiom = "a record state threaded through foldl over a range, with a field update on every step and a second update on a bounce"

main :: Effect Unit
main = benchmark { size: 10000000, workload }

type Particle = { position :: Int, velocity :: Int, bounces :: Int }

workload :: Int -> String
workload n = do
  let final = foldl step { position: 0, velocity: 7, bounces: 0 } (Array.range 1 n)
  show final.position <> " " <> show final.velocity <> " " <> show final.bounces

step :: Particle -> Int -> Particle
step particle _ = do
  let moved = particle { position = particle.position + particle.velocity }
  if moved.position > 1000 || moved.position < -1000 then
    moved { velocity = negate moved.velocity, bounces = moved.bounces + 1 }
  else moved
