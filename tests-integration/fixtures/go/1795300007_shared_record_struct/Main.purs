module Main where

import Prelude

import Header (header)
import Variable (variable)

-- | Two modules' structs cannot both represent records with the same fields: the program would
-- | need each record to be both structs at once.
main :: String
main = header.name <> variable.name
