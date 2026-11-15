module Main where

import Prelude

import Data.List (List(..), (:))

-- 160 bytes of strings: past the limit for data that cells copy, within the
-- limit for data that is only returned and matched.
data Outcome
  = Found String String String String String String String String String String
  | Missing

data Entry
  = Entry String String String String String String String String String String
  | Blank

search :: Int -> Int -> Outcome
search target key
  | key == target = Found (show key) "b" "c" "d" "e" "f" "g" "h" "i" "j"
  | key > 9 = Missing
  | otherwise = search target (key + 1)

describe :: Outcome -> String
describe (Found first _ _ _ _ _ _ _ _ last) = first <> last
describe Missing = "missing"

entries :: List Entry
entries = Entry "k" "l" "m" "n" "o" "p" "q" "r" "s" "t" : Blank : Nil

firsts :: List Entry -> String
firsts Nil = ""
firsts (Entry first _ _ _ _ _ _ _ _ _ : rest) = first <> firsts rest
firsts (Blank : rest) = "_" <> firsts rest

main :: { found :: String, missing :: String, entries :: String }
main =
  { found: describe (search 3 0)
  , missing: describe (search 12 0)
  , entries: firsts entries
  }
