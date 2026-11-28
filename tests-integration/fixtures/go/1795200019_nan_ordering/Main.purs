module Main where

import Prelude

import Data.Number as Number
import Data.Ord (between, clamp)
import Effect (Effect)

-- | `>` and `>=` on Number answer as `compare` does, which puts NaN after every number, both at
-- the known instance and through a dictionary parameter; `<` and `<=` are false for NaN.
above :: forall a. Ord a => a -> a -> Boolean
above x y = x > y

aboveOrEqual :: forall a. Ord a => a -> a -> Boolean
aboveOrEqual x y = x >= y

main :: Effect Int
main = pure
  ( (if between 0.0 1.0 Number.nan then 1 else 0)
      + (if between 0.0 Number.nan 0.5 then 2 else 0)
      + (if between Number.nan 1.0 0.5 then 4 else 0)
      + (if Number.nan >= 0.0 then 8 else 0)
      + (if Number.nan > 1.0 then 16 else 0)
      + (if above Number.nan 1.0 then 32 else 0)
      + (if aboveOrEqual Number.nan Number.nan then 64 else 0)
      + (if Number.isNaN (clamp 0.0 1.0 Number.nan) then 128 else 0)
      + (if compare Number.nan 0.0 == GT then 256 else 0)
  )
