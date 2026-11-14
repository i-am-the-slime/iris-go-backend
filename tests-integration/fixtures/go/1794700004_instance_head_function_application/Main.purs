module Main where

import Prelude

import Data.Foldable (foldMap)
import Data.Monoid.Endo (Endo(..))
import Data.Newtype (unwrap)

main :: Int
main = unwrap (foldMap (\x -> Endo (\acc -> acc * 10 + x)) [ 1, 2, 3 ]) 0
