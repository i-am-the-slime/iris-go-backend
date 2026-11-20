module Main where

import Prelude

import Buffers (freeze, new, size)

-- | An `unsafeCoerce` between two foreign data types whose Go types differ is reported where it is
-- | written, with both types as PureScript and Go see them.
main :: String
main = show (size (freeze (new 3)))
