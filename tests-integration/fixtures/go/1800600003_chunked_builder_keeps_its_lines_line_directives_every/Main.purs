module Main where

import Prelude

import Effect (Effect)
import Journal (log)

data Expr
  = Add Expr Expr
  | Val Int
  | Var Int

main :: Effect Unit
main = log (show (eval (sumTree 4 1)))

sumTree :: Int -> Int -> Expr
sumTree depth number
  | depth == 0 = leaf number
  | otherwise = Add (sumTree below (number + 1)) (sumTree below (max (number - 1) 0))
  where
  below = depth - 1

leaf :: Int -> Expr
leaf number = if number == 0 then Var 1 else Val number

eval :: Expr -> Int
eval = case _ of
  Var _ -> 0
  Val number -> number
  Add left right -> eval left + eval right
