module Main where

import Prelude

import Data.Traversable (traverse)

newtype Scaled a = Scaled (Int -> Int -> a)

instance Functor Scaled where
  map f (Scaled g) = Scaled \scale offset -> f (g scale offset)

instance Apply Scaled where
  apply (Scaled f) (Scaled g) = Scaled \scale offset -> f scale offset (g scale offset)

instance Applicative Scaled where
  pure a = Scaled \_ _ -> a

scaled :: Int -> Scaled Int
scaled n = Scaled \scale offset -> n * scale + offset

runScaled :: forall a. Scaled a -> a
runScaled (Scaled f) = f 3 1

main :: Array Int
main = runScaled (traverse scaled [ 1, 2, 3 ])
