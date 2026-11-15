module Main where

import Prelude

describe :: forall a. Show a => Array Int -> String -> Int -> a -> String
describe depths label 0 value = label <> show depths <> ": " <> show value
describe depths label depth value =
  describe (depths <> [ depth ]) (label <> ">") (depth - 1) [ value ]

main :: Array String
main = [ describe [] "" 2 true ]
