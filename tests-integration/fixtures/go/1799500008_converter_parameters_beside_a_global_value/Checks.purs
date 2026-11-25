module Checks where

import Prelude
import Data.Either (Either(..))

value :: Int -> Either String Int
value n = if n > 100 then Left "too big" else if n > 0 then Right n else value (n + 10)

checked :: Array Int -> Array (Either String Int)
checked = map value
