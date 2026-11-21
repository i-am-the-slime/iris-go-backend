module Main where

import Prelude

import Data.Either (Either(..))
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
import Data.Show.Generic (genericShow)
import Data.Tuple (Tuple(..))

data Shape = Circle Number | Rect { w :: Int, h :: Int } | Empty | Pair Int (Maybe Int)

derive instance Generic Shape _

instance Show Shape where
  show shape = genericShow shape

data Colour = Red | Mixed Colour Colour | Named String

derive instance Generic Colour _

instance Show Colour where
  show colour = genericShow colour

newtype Meters = Meters Number

derive instance Generic Meters _

instance Show Meters where
  show = genericShow

newtype Wrapped = Wrapped { a :: Int }

derive newtype instance Show Wrapped

data Point = Point Int Int

instance Show Point where
  show (Point x y) = "<" <> show x <> "," <> show y <> ">"

main :: Array String
main =
  [ show [ 1, 2, 3 ]
  , show ([] :: Array Int)
  , show [ [ 1 ], [], [ -2, 3 ] ]
  , show { name: "x", age: 3, b: true, z: [ 1.5 ] }
  , show [ { x: Just 1, y: Nothing :: Maybe Int } ]
  , show [ Left 1, Right "x" ] <> show [ Tuple 'a' [ Just 2.5 ] ]
  , show [ Circle 1.0, Rect { w: 1, h: -2 }, Empty, Pair (-3) (Just (-4)) ]
  , show [ Red, Mixed Red (Named "x\"y") ]
  , show [ Meters 1.0 ] <> show [ 1.0 ]
  , show [ Wrapped { a: 1 } ]
  , show [ Point 1 2 ]
  ]
