module Main where

import Prelude

import Effect (Effect)

main :: Effect (Array String)
main = pure
  [ show (sumOf (\i -> i * 3) 1000 0 0)
  , show (sumOf (\i -> i + 7) 1000 0 0)
  , show (sumWith (\i -> i * 5) 1000)
  ]
  where
  sumOf f count index total
    | index >= count = total
    | otherwise = sumOf f count (index + 1) (total + f index)

  sumWith f count = go 0 0
    where
    go index total
      | index >= count = total
      | otherwise = go (index + 1) (total + f index)
