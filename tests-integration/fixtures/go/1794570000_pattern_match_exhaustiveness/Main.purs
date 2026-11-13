module Main where

import Prelude

import Data.Maybe (Maybe(..))
import Partial.Unsafe (unsafePartial)

data Light = Red | Amber | Green

data Shape = Circle Int | Rectangle Int Int

name :: Light -> String
name = case _ of
  Red -> "red"
  Amber -> "amber"
  Green -> "green"

area :: Shape -> Int
area (Circle radius) = 3 * radius * radius
area (Rectangle width height) = width * height

pair :: Maybe Int -> Maybe Int -> Int
pair (Just left) (Just right) = left + right
pair (Just left) Nothing = left
pair Nothing _ = 0

command :: String -> Int
command "start" = 1
command "stop" = 2
command _ = 0

size :: Boolean -> Int -> String
size large number = case large of
  true
    | number > 100 -> "huge"
    | otherwise -> "large"
  false -> "small"

sum :: { left :: Int, right :: Int } -> Int
sum record = left + right
  where
  { left, right } = record

fromJust :: forall a. Partial => Maybe a -> a
fromJust (Just value) = value

main :: Array String
main =
  map name [ Red, Amber, Green ]
    <> map (show <<< area) [ Circle 1, Rectangle 2 3 ]
    <> map (show <<< pair (Just 1)) [ Just 2, Nothing ]
    <> map (show <<< command) [ "start", "jump" ]
    <> map (size true) [ 500, 5 ]
    <> map (show <<< sum) [ { left: 1, right: 2 } ]
    <> map (\value -> unsafePartial (fromJust value)) [ Just "here" ]
