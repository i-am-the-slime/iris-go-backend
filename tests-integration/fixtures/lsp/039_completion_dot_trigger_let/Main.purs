module Main where

import Data.Maybe (Maybe(..), fromMaybe)

rec :: { something :: { nested :: String }, another :: String }
rec = { something: { nested : "value"} , another: "value2" }

x :: String
x = do
  let fallback = "fb"
  let callback = rec.something
  callback.
--         #
