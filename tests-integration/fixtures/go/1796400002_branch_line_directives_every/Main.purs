module Main where

import Prelude

import Data.Either (Either(..))
import Effect (Effect)
import Effect.Exception (throw)
import Effect.Ref as Ref

data Tree = Leaf | Node Tree Int Tree

data Suit = Hearts | Spades

instance Show Suit where
  show Hearts = "hearts"
  show Spades = "spades"

insert :: Int -> Tree -> Tree
insert x = case _ of
  Leaf -> Node Leaf x Leaf
  node@(Node left y right)
    | x < y -> Node (insert x left) y right
    | x > y -> Node left y (insert x right)
    | otherwise -> node

size :: Tree -> Int
size = case _ of
  Leaf -> 0
  Node left _ right -> size left + 1 + size right

describe :: Int -> String
describe n =
  if n < 0 then "negative"
  else if n == 0 then "zero"
  else "positive"

parse :: Int -> Either String Int
parse n
  | n > 100 = Left "too big"
  | otherwise = Right n

main :: Effect Unit
main = do
  counter <- Ref.new 3
  total <- Ref.read counter
  let tree = insert total (insert 1 (insert 5 Leaf))
  when (size tree /= 3) do
    throw "the size is wrong"
  when (show (if total > 2 then Hearts else Spades) /= "hearts") do
    throw "the suit is wrong"
  when (describe total /= "positive") do
    throw "the description is wrong"
  suits <- Ref.new Spades
  suit <- Ref.read suits
  case suit of
    Hearts ->
      throw "the suit is hearts"
    Spades ->
      Ref.write Hearts suits
  case parse total of
    Left problem ->
      throw problem
    Right parsed ->
      Ref.write (parsed + 1) counter
