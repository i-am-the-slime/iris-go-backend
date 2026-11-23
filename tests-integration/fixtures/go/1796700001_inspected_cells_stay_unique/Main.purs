module Main where

import Prelude

data Expr = Add Expr Expr | Mul Expr Expr | Val Int

expression :: Int -> Expr
expression depth
  | depth == 0 = Val 1
  | otherwise = Add (expression (depth - 1)) (Mul (Val depth) (expression (depth - 1)))

evaluate :: Expr -> Int
evaluate = case _ of
  Val value -> value
  Add left right -> evaluate left + evaluate right
  Mul left right -> evaluate left * evaluate right

doubled :: Expr -> Expr
doubled = case _ of
  Val value -> Val (value * 2)
  Add left right -> Add (doubled left) (doubled right)
  Mul left right -> Mul (doubled left) (doubled right)

swapped :: Expr -> Expr
swapped = case _ of
  Add left right -> Add (swapped right) (swapped left)
  Mul left right -> Mul (swapped right) (swapped left)
  value -> value

inspectedThenTransformed :: Int -> String
inspectedThenTransformed depth = do
  let tree = expression depth
  show (evaluate tree) <> " then " <> show (evaluate (doubled tree))

inspectedInARecord :: Int -> { inspected :: Int, transformed :: Int }
inspectedInARecord depth = do
  let tree = expression depth
  { inspected: evaluate tree, transformed: evaluate (swapped (doubled tree)) }

transformedBeforeInspected :: Int -> { first :: Int, second :: Int }
transformedBeforeInspected depth = do
  let tree = expression depth
  { first: evaluate (doubled tree), second: evaluate tree }

inspectionUsedAfterTheTransform :: Int -> Int
inspectionUsedAfterTheTransform depth = do
  let tree = expression depth
  let before = evaluate tree
  let after = evaluate (doubled tree)
  after * 100000 + before

main :: Array String
main = do
  let record = inspectedInARecord 4
  let reversed = transformedBeforeInspected 4
  [ inspectedThenTransformed 4
  , show record.inspected <> " then " <> show record.transformed
  , show reversed.first <> " before " <> show reversed.second
  , show (inspectionUsedAfterTheTransform 4)
  ]
