module Compat.Recursion.Schemes where

import Prelude

import Data.Functor.Mu (Mu, roll, unroll)
import Data.Functor.Nu (Nu, observe, unfold)
import Data.List (List(..), (:))
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Console (log)
import Matryoshka (Algebra, Coalgebra, GAlgebra, ana, cata, embed, histo, hylo, para, project)
import Control.Comonad.Cofree (Cofree, head, tail)

data ExprF a
  = Literal Int
  | Add a a
  | Multiply a a
  | Negate a

derive instance Functor ExprF

type Expr = Mu ExprF

literal :: Int -> Expr
literal = embed <<< Literal

add :: Expr -> Expr -> Expr
add a b = embed (Add a b)

multiply :: Expr -> Expr -> Expr
multiply a b = embed (Multiply a b)

negate' :: Expr -> Expr
negate' = embed <<< Negate

evaluate :: Algebra ExprF Int
evaluate = case _ of
  Literal n -> n
  Add a b -> a + b
  Multiply a b -> a * b
  Negate a -> negate a

render :: Algebra ExprF String
render = case _ of
  Literal n -> show n
  Add a b -> "(" <> a <> " + " <> b <> ")"
  Multiply a b -> a <> " * " <> b
  Negate a -> "-" <> a

-- | Shows `Negate` of a literal without parentheses, using the original subterm.
renderPara :: GAlgebra (Tuple Expr) ExprF String
renderPara = case _ of
  Literal n -> show n
  Add (Tuple _ a) (Tuple _ b) -> a <> "+" <> b
  Multiply (Tuple _ a) (Tuple _ b) -> a <> "*" <> b
  Negate (Tuple original a) -> case project original of
    Literal _ -> "-" <> a
    _ -> "-(" <> a <> ")"

data ListF a r = NilF | ConsF a r

derive instance Functor (ListF a)

range :: Coalgebra (ListF Int) Int
range n = if n <= 0 then NilF else ConsF n (n - 1)

sumList :: Algebra (ListF Int) Int
sumList = case _ of
  NilF -> 0
  ConsF a r -> a + r

toList :: Algebra (ListF Int) (List Int)
toList = case _ of
  NilF -> Nil
  ConsF a r -> a : r

fibonacci :: Int -> Int
fibonacci = histo step <<< (ana natural :: Int -> Mu Maybe)
  where
  natural n = if n <= 0 then Nothing else Just (n - 1)
  step :: Maybe (Cofree Maybe Int) -> Int
  step = case _ of
    Nothing -> 0
    Just previous -> case tail previous of
      Nothing -> 1
      Just beforePrevious -> head previous + head beforePrevious

naturals :: Nu (ListF Int)
naturals = unfold 0 \n -> ConsF n (n + 1)

takeNu :: Int -> Nu (ListF Int) -> List Int
takeNu n stream
  | n <= 0 = Nil
  | otherwise = case observe stream of
      NilF -> Nil
      ConsF a rest -> a : takeNu (n - 1) rest

main :: Effect Unit
main = do
  let expression = add (literal 2) (multiply (literal 3) (negate' (add (literal 4) (literal 1))))
  log (cata render expression <> " = " <> show (cata evaluate expression))
  log (para renderPara (add (negate' (literal 1)) (negate' (multiply (literal 2) (literal 3)))))
  log (show (hylo sumList range 100))
  log (show (cata toList (ana range 5 :: Mu (ListF Int))))
  log (show (takeNu 5 naturals))
  log (show (case unroll (roll (Literal 9) :: Expr) of
    Literal n -> n
    _ -> 0))
  log (show (map fibonacci [ 0, 1, 2, 10 ]))
