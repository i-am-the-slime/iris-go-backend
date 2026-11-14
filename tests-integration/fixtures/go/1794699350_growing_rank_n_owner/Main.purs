module Main where

import Prelude

import Data.Tuple (Tuple(..))

newtype Sampler a = Sampler (forall b. Array (a -> b) -> Array b)

sampleWith :: forall a b. Sampler a -> Array (a -> b) -> Array b
sampleWith (Sampler sample) = sample

constant :: forall a. a -> Sampler a
constant value = Sampler \questions -> map (_ $ value) questions

instance Functor Sampler where
  map f (Sampler sample) = Sampler \questions -> sample (map (_ <<< f) questions)

instance Apply Sampler where
  apply (Sampler functions) (Sampler values) = Sampler \questions ->
    map (\function (Tuple question value) -> question (function value)) (functions (map (const identity) questions))
      <*> values (map Tuple questions)

main :: Array Int
main = sampleWith ((+) <$> constant 1 <*> constant 10) [ identity, (_ * 2) ]
