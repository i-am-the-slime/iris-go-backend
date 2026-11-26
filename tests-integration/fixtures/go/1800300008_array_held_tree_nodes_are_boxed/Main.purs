module Main where

import Prelude

import Data.Array as Array
import Data.Maybe (fromMaybe)

-- | A node that keeps keys, values and children in arrays is 72 bytes: copying the children, as
-- | every persistent write does, copies pointers to the nodes, not the nodes.
data Wide = Wide (Array Int) (Array String) (Array Wide)

-- | A node of one Int and its children is small enough to stay in its parent's array.
data Rose = Rose Int (Array Rose)

-- | Points that are no tree stay in their array too.
type Point = { x :: Number, y :: Number, z :: Number, w :: Number, label :: String }

replaced :: Int -> Wide -> Wide -> Wide
replaced index child (Wide keys labels children) =
  Wide keys labels (Array.updateAt index child children # fromMaybe children)

size :: Wide -> Int
size (Wide keys _ children) = Array.length keys + Array.foldl (\total child -> total + size child) 0 children

roseTotal :: Rose -> Int
roseTotal (Rose here children) = here + Array.foldl (\total child -> total + roseTotal child) 0 children

main :: Array Int
main = do
  let leaf = Wide [ 1, 2 ] [ "a", "b" ] []
  let tree = replaced 0 (Wide [ 3 ] [ "c" ] []) (Wide [ 5 ] [ "e" ] [ leaf, leaf ])
  let rose = Rose 1 [ Rose 2 [], Rose 3 [ Rose 4 [] ] ]
  let points = [ { x: 1.0, y: 2.0, z: 3.0, w: 4.0, label: "p" } ] :: Array Point
  [ size tree, roseTotal rose, Array.length points ]
