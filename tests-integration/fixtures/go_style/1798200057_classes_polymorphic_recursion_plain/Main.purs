module T.PolyRecPlain where

import Prelude

import Effect (Effect)
import Effect.Console (log)

data Nested a = Flat a | Nest (Nested (Array a))

depth :: forall a. Nested a -> Int
depth = case _ of
  Flat _ -> 0
  Nest inner -> 1 + depth inner

countLeaves :: forall a. Nested a -> Int
countLeaves = go 1
  where
  go :: forall b. Int -> Nested b -> Int
  go width = case _ of
    Flat _ -> width
    Nest inner -> go (width * 2) inner

main :: Effect Unit
main = do
  log (show (depth (Nest (Nest (Flat [ [ 'a' ] ])))))
  log (show (countLeaves (Nest (Nest (Flat [ [ 'a' ] ])))))
