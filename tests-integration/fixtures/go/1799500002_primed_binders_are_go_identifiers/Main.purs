module Main where

import Prelude

import Data.Array (filter, length, (..))
import Data.Foldable (sum)
import Effect (Effect)
import Journal (log)

describe :: Array Int -> Int
describe xs = case xs >>= \x -> [x, x] of
  [x] -> x
  xs' -> length xs'

punned :: { x' :: Int, y :: Int } -> Int
punned { x', y } = x' + y

triangle :: Int -> Int
triangle n = go' n 0
  where
  go' 0 total' = total'
  go' k total' = go' (k - 1) (total' + k)

main :: Effect Unit
main = do
  let xs' = 1 .. 3
  let double' = \a' -> a' * 2
  let ys'' = map double' xs'
  log (show (describe xs'))
  log (show (sum ys'' + length (filter (\v' -> v' > 1) xs')))
  log (show (punned { x': 1, y: 2 }))
  log (show (triangle 4))
