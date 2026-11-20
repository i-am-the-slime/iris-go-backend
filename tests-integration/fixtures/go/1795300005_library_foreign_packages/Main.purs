module Main where

import Prelude

import Effect (Effect)
import Test.Assert (assert')
import Test.QuickCheck.Gen (float32ToInt32)

-- | A library without Go files of its own, such as `Test.Assert`, takes its foreign package from
-- iris-go's `ffi` packages; Go files next to a module's source, such as `Test.QuickCheck.Gen`'s,
-- take precedence.
main :: Effect Unit
main = assert' "reads the bits of a float" (float32ToInt32 1.5 == 1069547520)
