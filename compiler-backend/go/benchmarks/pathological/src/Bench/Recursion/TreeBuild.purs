module Bench.Recursion.TreeBuild where

import Prelude

import Bench.Harness (benchmark)
import Effect (Effect)

hypothesis :: String
hypothesis = "a naive recursive builder allocates millions of small short-lived tree nodes that a young-generation GC frees for almost nothing"

data Tree
  = Leaf
  | Node Tree Int Tree

main :: Effect Unit
main = benchmark { size: 20, workload }

workload :: Int -> String
workload depth = do
  let tree = build depth 1
  show (count tree) <> " " <> show (checksum tree) <> " " <> show (count (mirror tree))
  where
  build 0 _ = Leaf
  build d label = Node (build (d - 1) (label * 2)) label (build (d - 1) (label * 2 + 1))

  count Leaf = 0
  count (Node left _ right) = count left + 1 + count right

  checksum Leaf = 0
  checksum (Node left label right) = (checksum left * 31 + label + checksum right) `mod` 1000003

  mirror Leaf = Leaf
  mirror (Node left label right) = Node (mirror right) label (mirror left)
