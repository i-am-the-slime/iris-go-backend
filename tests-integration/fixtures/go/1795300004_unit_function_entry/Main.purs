module Main where

import Prelude

-- | A `Unit -> Unit` entry, as purescript-prelude's tests write `main :: AlmostEff`, is run like
-- JavaScript's `main()`, not printed.
main :: Unit -> Unit
main = do
  checked 1
  checked 2
  where
  checked :: Int -> Unit -> Unit
  checked n _ = if n > 0 then unit else unit
