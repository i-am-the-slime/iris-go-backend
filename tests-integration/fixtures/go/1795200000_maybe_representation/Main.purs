module Main where

import Prelude

import Data.Array (head)
import Data.Maybe (Maybe(..), fromMaybe, isJust)

opaque :: Int -> Int
opaque x = if x == 12345 then opaque x else x

positive :: Int -> Maybe Int
positive x = if x > 0 then Just (x + 1) else Nothing

initial :: Int -> Maybe Char
initial x = if x > 0 then Just 'c' else Nothing

large :: Int -> Maybe Boolean
large x = if x > 0 then Just (x > 5) else Nothing

data Tree = Leaf | Node Tree Int Tree

tree :: Int -> Maybe Tree
tree x = if x > 0 then Just (Node Leaf x Leaf) else Nothing

adder :: Int -> Maybe (Int -> Int)
adder x = if x > 0 then Just (\y -> y + x) else Nothing

name :: Int -> Maybe String
name x = if x > 0 then Just "yes" else Nothing

nested :: Int -> Maybe (Maybe Int)
nested x = if x > 0 then Just (positive (x - 1)) else Nothing

data Shape = Circle Int | Square Int Int

derive instance Eq Shape
derive instance Ord Shape

shape :: Int -> Maybe Shape
shape x = if x > 0 then Just (Circle x) else if x < -5 then Just (Square x x) else Nothing

sumTree :: Tree -> Int
sumTree Leaf = 0
sumTree (Node l x r) = sumTree l + x + sumTree r

showOrdering :: Ordering -> String
showOrdering = case _ of
  LT -> "LT"
  EQ -> "EQ"
  GT -> "GT"

main :: Array String
main =
  [ show (fromMaybe 0 (positive (opaque 10)))
  , show (positive (opaque 1) == positive (opaque 1))
  , showOrdering (compare (positive (opaque 1)) (positive (opaque 2)))
  , show (initial (opaque 1))
  , show (large (opaque 7))
  , show (map sumTree (tree (opaque 4)))
  , show (map (\f -> f 1) (adder (opaque 5)))
  , fromMaybe "no" (name (opaque 1))
  , show (nested (opaque 2))
  , show (shape (opaque (-7)) == shape (opaque (-7)))
  , showOrdering (compare (shape (opaque 7)) (shape (opaque (-7))))
  , show (isJust (tree (opaque 0)))
  , show (head [ positive (opaque 1), Nothing ])
  , case tree (opaque 1) of
      Just (Node _ x _) -> show x
      Just Leaf -> "leaf"
      Nothing -> "none"
  , case nested (opaque 2) of
      Just (Just x) -> show x
      Just Nothing -> "just nothing"
      Nothing -> "nothing"
  , case initial (opaque 1) of
      Just 'c' -> "c"
      Just _ -> "other"
      Nothing -> "none"
  , case large (opaque 7) of
      Just true -> "yes"
      Just false -> "no"
      Nothing -> "none"
  ]
