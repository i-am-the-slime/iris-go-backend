module Main where

import Prelude

import Clock (elapsed, now)
import Effect (Effect)
import Timer (seconds, timer)

-- | A foreign import whose module's Go files declare no function for it, and a foreign data type
-- | they declare no type for, are reported before Go sees them, naming the files and what they
-- | should declare.
main :: Effect Number
main = do
  start <- now
  passed <- elapsed start
  pure (passed + seconds (timer 1.0))
