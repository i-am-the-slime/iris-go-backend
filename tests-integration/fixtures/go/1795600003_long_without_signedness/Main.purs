module Main where

import Prelude

import Data.Int (decimal)
import Data.Int64.Internal as Internal

-- | A bare Long whose definition names neither Int64 nor UInt64 has no Go type to be.
unknown :: String
unknown = Internal.toString_ (Internal.add_ Internal.one_ Internal.one_) decimal

main :: Array String
main = [ unknown ]
