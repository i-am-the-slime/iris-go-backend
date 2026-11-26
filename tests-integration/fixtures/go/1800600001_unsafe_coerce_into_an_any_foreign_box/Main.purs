module Main where

import Prelude

import Boxes (Box, intoBox, outOfBox)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (maybe)
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Effect.Ref as Ref
import Journal (log)

main :: Effect Unit
main = do
  cell <- Ref.new (intoBox { name: "boxed" })
  boxed <- Ref.read cell
  log (outOfBox boxed).name
  log (nameAt 1 cache)
  log (show (countAt 2 cache))
  where
  cache :: Map Int Box
  cache = Map.fromFoldable
    [ 1 /\ intoBox { name: "first" }
    , 2 /\ intoBox 42
    ]

nameAt :: Int -> Map Int Box -> String
nameAt key boxes = Map.lookup key boxes # maybe "missing" readName
  where
  readName box = (outOfBox box :: { name :: String }).name

countAt :: Int -> Map Int Box -> Int
countAt key boxes = Map.lookup key boxes <#> outOfBox # maybe 0 identity
