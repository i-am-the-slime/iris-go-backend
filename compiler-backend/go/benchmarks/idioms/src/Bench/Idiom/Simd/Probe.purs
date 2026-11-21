module Bench.Idiom.Simd.Probe
  ( probe
  ) where

import Prelude

import Data.Array as Array
import Data.Maybe (fromMaybe)

-- | A few elements of a result, enough to check it without summing it (which would time a second
-- | kernel).
probe :: Array Number -> String
probe xs = show (Array.length xs) <> " " <> show (at 0) <> " " <> show (at (Array.length xs / 2)) <> " " <> show (at (Array.length xs - 1))
  where
  at i = fromMaybe 0.0 (Array.index xs i)
