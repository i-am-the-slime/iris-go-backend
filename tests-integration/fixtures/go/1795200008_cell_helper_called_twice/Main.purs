module Main where

import Prelude

import Control.Monad.Rec.Class (Step(..), tailRecM)
import Control.Monad.ST (run)
import Control.Monad.ST.Ref as STRef

-- tailRecM in ST applies its step twice; the step touches the cell, so it
-- stays in the cell's function and the cell is a plain local.
summedTo :: Int -> Int
summedTo n = run do
  total <- STRef.new 0
  let
    step i
      | i > n = pure (Done unit)
      | otherwise = do
          _ <- STRef.modify (_ + i) total
          pure (Loop (i + 1))
  tailRecM step 1
  STRef.read total

-- A helper that touches no cell stays one function, called twice.
scaled :: Int -> Array Int
scaled n = [ scale 1, scale 2 ]
  where
  scale x = n * 10 + x

main :: { total :: Int, scaled :: Array Int }
main = { total: summedTo 10, scaled: scaled 4 }
