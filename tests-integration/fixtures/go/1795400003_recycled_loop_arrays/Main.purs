module Main where

import Prelude

import Data.Array as Array
import Data.FoldableWithIndex (foldlWithIndex)

type Particle = { position :: Number, velocity :: Number }

-- | Each step reads every other particle while it builds the next array, so the step cannot write
-- | over the array it reads: it writes into the array of the step before last, and the loop
-- | allocates only for its first two steps.
attract :: Int -> Array Particle -> Array Particle
attract steps = go 0
  where
  go i particles
    | i >= steps = particles
    | otherwise = go (i + 1) (map move (Array.mapWithIndex (pull particles) particles))

  pull particles i particle = foldlWithIndex (towards i) particle particles

  towards i j acc other
    | i == j = acc
    | otherwise = acc { velocity = acc.velocity + (other.position - acc.position) * 0.001 }

  move particle = particle { position = particle.position + particle.velocity }

-- | A map that never reads the array recycles the same way.
doubleAll :: Int -> Array Int -> Array Int
doubleAll steps = go 0
  where
  go i values
    | i >= steps = values
    | otherwise = go (i + 1) (map (\value -> value * 2 + i) values)

-- | A filtered map appends into the recycled buffer, whose length changes from step to step.
shrink :: Array Int -> Array Int
shrink = go
  where
  go values
    | Array.length values <= 1 = values
    | otherwise = go (map (_ - 1) (Array.filter (_ > 2) values))

-- | The step keeps the array it replaces, so it is not free once the loop jumps: each step
-- | allocates.
withPrevious :: Int -> Array Int -> Array Int -> Array Int
withPrevious steps = go 0
  where
  go i previous values
    | i >= steps = previous <> values
    | otherwise = go (i + 1) values (map (_ + 1) values)

-- | Elements that hold arrays could refer to the array the loop replaces: each step allocates.
nested :: Int -> Array (Array Int) -> Array (Array Int)
nested steps = go 0
  where
  go i rows
    | i >= steps = rows
    | otherwise = go (i + 1) (map (\row -> row <> [ i ]) rows)

main :: Array String
main =
  [ show (attract 50 [ { position: 0.0, velocity: 0.0 }, { position: 1.0, velocity: 0.5 }, { position: 4.0, velocity: -0.25 } ])
  , show (doubleAll 10 [ 1, 2, 3 ])
  , show (shrink [ 9, 3, 7, 5, 4 ])
  , show (withPrevious 3 [ 0 ] [ 1, 2 ])
  , show (nested 3 [ [ 1 ], [ 2 ] ])
  ]
