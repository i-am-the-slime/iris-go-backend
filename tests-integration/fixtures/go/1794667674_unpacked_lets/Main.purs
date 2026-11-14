module Main where

import Prelude

import Data.Maybe (Maybe(..))

opaque :: Int -> Int
opaque x = if x == 12345 then opaque x else x

data Shape = Circle Int | Rectangle Int Int

-- A record read field by field never exists as a whole.
bounds :: Int -> Int
bounds n = do
  let box = { width: opaque n, height: opaque (n + 1) }
  box.width * box.height + box.width

-- A constructor matched twice resolves both matches.
area :: Int -> Int
area n = do
  let shape = Rectangle (opaque n) (opaque (n + 2))
  let width = case shape of
        Circle radius -> radius
        Rectangle w _ -> w
  let height = case shape of
        Circle radius -> radius
        Rectangle _ h -> h
  width * height

-- Passed on as a whole, the record stays one.
whole :: Int -> { x :: Int, y :: Int }
whole n = do
  let point = { x: opaque n, y: opaque n }
  if point.x > 0 then point else { x: 0, y: point.y }

-- A match the constructor cannot resolve keeps it.
nested :: Int -> Int
nested n = do
  let found = Just (Just (opaque n))
  case found of
    Just (Just value) -> value
    _ -> case found of
      Just _ -> 1
      Nothing -> 0

main :: Array Int
main = [ bounds 3, area 4, (whole 5).y, nested 6 ]
