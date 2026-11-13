module Main where

import Prelude

import Data.Array.NonEmpty (NonEmptyArray, cons')
import Data.Maybe (Maybe(..))
import Data.Semigroup.Traversable (traverse1)

halve :: Int -> Maybe Int
halve n = if n `mod` 2 == 0 then Just (n / 2) else Nothing

main :: Maybe (NonEmptyArray Int)
main = traverse1 halve (cons' 2 [ 4, 8 ])
