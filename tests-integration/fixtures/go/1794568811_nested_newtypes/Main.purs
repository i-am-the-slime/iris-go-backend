module Main where

import Prelude

newtype Box a = Box a

instance Show a => Show (Box a) where
  show (Box a) = "Box " <> show a

main :: String
main = show (Box (Box [ 1, 2 ]))
