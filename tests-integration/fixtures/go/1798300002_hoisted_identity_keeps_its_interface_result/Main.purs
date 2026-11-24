module Main where

import Prelude

import Data.Identity (Identity(..))
import Data.Newtype (un)
import Data.Tuple (Tuple(..), snd)
import Effect (Effect)
import Effect.Console (log)

data Tree a = Leaf String (Int -> a) | Node String (Array (Tree a))

instance Functor Tree where
  map change (Leaf name run) = Leaf name (run >>> change)
  map change (Node name children) = Node name (map (map change) children)

newtype Collect m a = Collect (m (Tuple Unit (Array (Tree a))))

mapCollect :: forall m n a b. Functor n => (m ~> n) -> (a -> b) -> Collect m a -> Collect n b
mapCollect hoist change (Collect inner) = Collect ((hoist >>> map (map (map (map change)))) inner)

collected :: Collect Identity Int
collected = Collect (Identity (Tuple unit [ Node "around" [ Leaf "fixture" (_ + 1) ] ]))

main :: Effect Unit
main = log (show (map run (snd (un Identity (unwrap (mapCollect identity show collected))))))
  where
  unwrap (Collect inner) = inner
  run (Leaf name value) = name <> " " <> value 41
  run (Node name children) = name <> " " <> show (map run children)
