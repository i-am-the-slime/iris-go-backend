module Main where

import Prelude

import Data.Array (foldl, foldr)
import Data.Maybe (Maybe(..))
import Data.String.CodeUnits (charAt)

opaque :: Int -> Int
opaque x = if x == 12345 then opaque x else x

data Light = Red | Amber | Green

derive instance Eq Light

light :: Int -> Light
light n = if n > 10 then Red else if n > 5 then Amber else Green

total :: Array Int -> Int
total xs = foldl add 0 xs

shown :: Array Int -> Array String
shown xs = map show xs

joined :: Array Int -> String
joined xs = foldr (\x rest -> show x <> "," <> rest) "" xs

initial :: String -> String
initial text = case charAt 0 text of
  Just 'a' -> "starts with a"
  Just _ -> "starts otherwise"
  Nothing -> "empty"

main :: Array String
main =
  [ show (total [ 1, 2, opaque 3 ])
  , show (shown [ 4, opaque 5 ])
  , joined [ 6, opaque 7 ]
  , initial "abc"
  , show (light (opaque 7) == light (opaque 12))
  , show (light (opaque 3) == Green)
  ]
