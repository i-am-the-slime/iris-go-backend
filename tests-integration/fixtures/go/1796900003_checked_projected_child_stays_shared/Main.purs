module Main where

import Prelude

import Data.Foldable (sum)
import Data.List (List(..), filter, length, (:))
import RedBlack (Tree(..), checksum, insert, size, valid)

left :: Tree -> Tree
left = case _ of
  Node _ l _ _ _ -> l
  Leaf -> Leaf

probe :: Int -> Tree -> { child :: Tree, grown :: Tree }
probe key tree = do
  let child = left tree
  { child, grown: insert key true tree }

projectedChild :: Int -> { probed :: Int, trees :: List Tree }
projectedChild steps = go Leaf Nil 0 steps
  where
  go tree kept probed n
    | n <= 0 = { probed, trees: tree : kept }
    | n `mod` 50 == 0 = do
        let probedTrees = probe (n + 100000) (insert (n * 2 + 1) true tree)
        go tree (probedTrees.grown : kept) (probed + checksum probedTrees.child) (n - 1)
    | otherwise = do
        let next = insert (n * 2) (n `mod` 3 == 0) tree
        go next (if n `mod` 7 == 0 then next : kept else kept) probed (n - 1)

main :: Array Int
main = do
  let result = projectedChild 1000
  [ result.probed
  , length result.trees
  , sum (map size result.trees)
  , sum (map checksum result.trees)
  , length (filter (not <<< valid) result.trees)
  ]
