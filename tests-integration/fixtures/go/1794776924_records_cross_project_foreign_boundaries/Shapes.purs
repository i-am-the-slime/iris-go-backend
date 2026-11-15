module Shapes where

import Data.Nullable (Nullable)

type Shape = { kind :: String, size :: Int }

foreign import measure :: String -> Nullable (Array Shape)

foreign import describe :: { name :: String, sides :: Int } -> String
