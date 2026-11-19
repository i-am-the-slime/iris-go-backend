module Main where

import Prelude

import Data.Either (Either(..), either)
import Data.List (List(..))
import Data.List as List
import Data.Maybe (Maybe(..))
import Effect (Effect)

data Shape
  = Leaf (List Int)
  | Branch Shape { items :: Int, flags :: Array Unit } Shape
  | Wrap Shape

-- | Two alternatives match constructors of the hoisted scrutinee's cell, which each would reuse
-- for the result they build.
rebuild :: Either Int Int -> Shape
rebuild = either (\_ -> Leaf Nil) \_ -> case Leaf (List.fromFoldable []) of
  Branch (Wrap _) { items: _, flags: _ } (Branch _ _ _) -> Leaf (List.fromFoldable [])
  Leaf (Cons _ _) -> Leaf (List.fromFoldable [])
  _ -> Leaf (List.fromFoldable [ 1 ])

main :: Effect Int
main = pure case rebuild (Right 0) of
  Leaf (Cons n _) -> n
  _ -> 0
