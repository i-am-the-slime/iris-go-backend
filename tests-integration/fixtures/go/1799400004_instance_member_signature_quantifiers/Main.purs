module Main where

import Prelude

import Data.Array (catMaybes)
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Journal (log)

newtype Box a = Box (Array a)

class Squash f where
  squash :: forall a. f (Maybe a) -> f a
  pairUp :: forall a b. f a -> f b -> f { left :: a, right :: b }

instance Squash Box where
  squash :: forall item. Box (Maybe item) -> Box item
  squash (Box items) = Box (keep items)
    where
    keep :: Array (Maybe item) -> Array item
    keep = catMaybes
  pairUp :: forall x y. Box x -> Box y -> Box { left :: x, right :: y }
  pairUp (Box lefts) (Box rights) = Box (join (map (\left -> map { left, right: _ } rights) lefts))

unbox :: forall a. Box a -> Array a
unbox (Box items) = items

main :: Effect Unit
main = do
  log (show (unbox (squash (Box [ Just 1, Nothing, Just 3 ]))))
  log (show (unbox (squash (Box [ Just "a", Nothing ]))))
  log (show (map (\{ left, right } -> show left <> right) (unbox (pairUp (Box [ 1, 2 ]) (Box [ "x" ])))))
