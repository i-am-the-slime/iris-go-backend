module Main where

import Prelude

import Data.Array ((..))
import Data.Lens (Lens, lens, over, set, view)

data Validated a = Fresh a | Modified a

derive instance Functor Validated

_Validated :: forall a b. Lens (Validated a) (Validated b) a b
_Validated = flip lens ($>) $ case _ of
  Fresh a -> a
  Modified a -> a

isModified :: forall a. Validated a -> Boolean
isModified = case _ of
  Fresh _ -> false
  Modified _ -> true

touch :: Int -> Validated Int
touch n = if n > 2 then Modified n else Fresh n

main :: Array String
main = map describe (1 .. 4)
  where
  describe n = do
    let touched = over _Validated (_ * 10) (touch n)
    let renamed = set _Validated (show n) touched
    show (view _Validated touched) <> " " <> view _Validated renamed <> " " <> show (isModified renamed)
