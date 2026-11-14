module Main where

import Prelude

import Native as Native

nest :: forall a. Show a => Int -> a -> String
nest 0 value = show value
nest n value = nest (n - 1) [ value ]

main :: Array String
main = [ nest 3 'x', Native.describe 1 ]
