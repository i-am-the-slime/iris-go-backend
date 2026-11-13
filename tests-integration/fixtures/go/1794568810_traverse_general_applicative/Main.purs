module Main where

import Prelude

import Data.Either (Either(..))
import Data.Traversable (traverse)

positive :: Int -> Either String Int
positive n = if n > 0 then Right n else Left ("not positive: " <> show n)

main :: Array (Either String (Array Int))
main = [ traverse positive [ 1, 2, 3 ], traverse positive [ 1, -2, 3 ] ]
