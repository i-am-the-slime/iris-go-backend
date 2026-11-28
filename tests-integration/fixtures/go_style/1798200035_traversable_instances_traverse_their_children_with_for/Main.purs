module Repro.R06 where

-- Same family as the known `<#>` polyrec false positive, but via `for` (flipped traverse)
-- inside a Traversable instance. Go: "cannot specialize Data.Traversable.for: polymorphic recursion ..."
import Prelude

import Data.Foldable (class Foldable, foldMap, foldl, foldr)
import Data.Maybe (Maybe(..))
import Data.Traversable (class Traversable, for, traverse)
import Effect (Effect)
import Effect.Console (log)

data Rose a = Rose a (Array (Rose a))

instance Functor Rose where
  map f (Rose a kids) = Rose (f a) (map (map f) kids)
instance Foldable Rose where
  foldr f z (Rose a kids) = f a (foldr (\kid acc -> foldr f acc kid) z kids)
  foldl f z (Rose a kids) = foldl (\acc kid -> foldl f acc kid) (f z a) kids
  foldMap f (Rose a kids) = f a <> foldMap (foldMap f) kids
instance Traversable Rose where
  traverse f (Rose a kids) = Rose <$> f a <*> for kids (traverse f)
  sequence = traverse identity

main :: Effect Unit
main = for (Rose 1 [ Rose 2 [] ]) (\n -> Just n) # map (foldl (+) 0) # show # log
