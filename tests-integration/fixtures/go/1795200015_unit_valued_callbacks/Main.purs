module Main where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl, foldr)
import Effect (Effect)

units :: Array Unit
units = Array.nub [ unit, unit ]

main :: Effect Int
main = do
  let folded = foldr (\_ accumulator -> accumulator) unit units
  let scanned = Array.scanl (\_ _ -> unit) folded [ 1, 2 ]
  let zipped = Array.zipWith (\_ _ -> unit) [ 1 ] units
  let ignore = foldl (\_ _ -> \_ -> unit) (\_ -> unit) [ 1 ] :: Int -> Unit
  let mapped = map ignore [ 1, 2, 3 ]
  pure
    ( Array.length units
        + Array.length scanned * 10
        + Array.length zipped * 100
        + Array.length mapped * 1000
    )
