module Main where

import Prelude

import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Console (log)

data Phases f a
  = Nil a
  | Cons (forall r. (forall y z. (y -> z -> a) -> f y -> Phases f z -> r) -> r)

cons' :: forall f a b c. (a -> b -> c) -> f a -> Phases f b -> Phases f c
cons' c f fs = Cons \res -> res c f fs

index' :: forall f a. Functor f => Int -> Phases f a -> Maybe (f Unit)
index' _ (Nil _) = Nothing
index' i (Cons unwrap)
  | i < 0 = Nothing
  | i == 0 = unwrap \_ f _ -> Just (void f)
  | otherwise = unwrap \_ _ fs -> index' (i - 1) fs

phases :: Phases Array Int
phases = cons' (\x _ -> x) [ 1, 2 ] (cons' (\_ y -> y) [ 3 ] (Nil 4))

main :: Effect Unit
main = do
  log (show (index' 0 phases))
  log (show (index' 1 phases))
  log (show (index' 2 phases))
