module Main where

import Prelude

import Partial.Unsafe (unsafeCrashWith)

newtype Combine = Combine (Int -> Int -> Int)

combineWith :: Int -> Combine
combineWith n
  | n > 0 = Combine \a b -> a * n + b
  | otherwise = unsafeCrashWith "a positive weight"

apply :: Combine -> Int -> Int -> Int
apply (Combine f) a b = f a b

main :: Array Int
main = [ apply (combineWith 2) 3 4, apply (combineWith 5) 1 1 ]
