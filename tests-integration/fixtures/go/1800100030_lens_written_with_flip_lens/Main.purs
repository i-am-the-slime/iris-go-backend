module Main where

import Prelude

import Data.Lens (Lens, lens, set, view)

data Validated a = Fresh a | Modified a

derive instance Functor Validated

_Validated :: forall a b. Lens (Validated a) (Validated b) a b
_Validated = flip lens ($>) valueOf
  where
  valueOf = case _ of
    Fresh a -> a
    Modified a -> a

setFresh :: Int -> Int
setFresh n = view _Validated (set _Validated n (Fresh 0))

main :: String
main = show (setFresh 3)
