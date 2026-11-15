module Main where

import Prelude

import Data.Nullable (Nullable, nullable)
import Shapes (Shape, describe, measure)

-- `measure` and `describe` are implemented by go-ffi/Shapes.go, which cannot name the structs
-- generated for these records: a record crosses as a Foreign object table, and a Nullable of a
-- converted value as a pointer to the converted value.
main :: String
main = describe { name: "square", sides: 4 } <> ": " <> nullable (measure "square") "unknown" sizes

sizes :: Array Shape -> String
sizes shapes = show (map _.size shapes)
