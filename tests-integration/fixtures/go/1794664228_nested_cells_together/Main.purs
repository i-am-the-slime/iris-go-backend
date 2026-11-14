module Main where

import Prelude

data Expr = Val Int | Add Expr Expr | Mul Expr Expr | Sub Expr Expr

data List a = Nil | Cons a (List a)

build :: Int -> Expr
build 0 = Val 1
build n = Add (Mul (Val n) (build (n - 1))) (Sub (build (n - 1)) (Val 1))

twoCellsAreAllocatedOneByOne :: Int -> Expr
twoCellsAreAllocatedOneByOne n = Add (build n) (Val n)

loopLinkedCellsAreChunked :: Int -> List Int
loopLinkedCellsAreChunked count = go count Nil
  where
  go remaining list =
    if remaining <= 0 then list
    else go (remaining - 1) (Cons remaining (Cons (remaining * 10) list))

mirror :: Expr -> Expr
mirror (Add left right) = Add (mirror right) (mirror left)
mirror (Mul left right) = Mul (mirror right) (mirror left)
mirror (Sub left right) = Sub (mirror right) (mirror left)
mirror value = value

evaluate :: Expr -> Int
evaluate (Val value) = value
evaluate (Add left right) = evaluate left + evaluate right
evaluate (Mul left right) = evaluate left * evaluate right
evaluate (Sub left right) = evaluate left - evaluate right

onlyEvaluatedWhenPositive :: Int -> Boolean
onlyEvaluatedWhenPositive n = n > 0 && evaluate (Add (Val n) (Mul (Val 2) (Val n))) > 5

total :: List Int -> Int
total Nil = 0
total (Cons value rest) = value + total rest

main
  :: Int
  -> { built :: Int
     , mirrored :: Int
     , two :: Int
     , linked :: Int
     , literal :: Int
     , positive :: Boolean
     , negative :: Boolean
     }
main n =
  { built: evaluate (build 4)
  , mirrored: evaluate (mirror (build 3))
  , two: evaluate (twoCellsAreAllocatedOneByOne 2)
  , linked: total (loopLinkedCellsAreChunked 5)
  , literal: total (Cons n (Cons 2 (Cons 3 Nil)))
  , positive: onlyEvaluatedWhenPositive n
  , negative: onlyEvaluatedWhenPositive (negate n)
  }
