module Main where

import Prelude

import Data.Either (either)
import Data.Foldable (foldl)
import Foreign.Object (Object)
import Foreign.Object as Object
import Yoga.JSON (readJSON, writeJSON)

inserted :: Array String -> Object Int
inserted = foldl (\table word -> Object.insert word (Object.size table) table) Object.empty

main :: Array String
main = [ written, either (const "unreadable") (show <<< Object.keys) read ]
  where
  written = writeJSON (inserted [ "b", "10", "a", "2" ])
  read = readJSON written :: _ (Object Int)
